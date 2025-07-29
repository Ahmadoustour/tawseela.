import os
import hashlib
import time
import schedule
import requests
import pandas as pd
import numpy as np
import json
import joblib
import threading
import shutil
import telegram.error
import binance.exceptions
import logging
import sys
import traceback
import platform
import psutil
import holidays
import sklearn
from logging.handlers import RotatingFileHandler
from datetime import datetime, timedelta, time
from binance.client import Client
from binance.exceptions import BinanceAPIException
from telegram import Bot
from telegram.constants import ParseMode
from telethon.sync import TelegramClient
from dotenv import load_dotenv
from ta.trend import EMAIndicator, ADXIndicator, MACD
from ta.momentum import RSIIndicator
from ta.volatility import BollingerBands
from xgboost import XGBClassifier
from bs4 import BeautifulSoup
from textblob import TextBlob
from sklearn.pipeline import Pipeline
from sklearn.preprocessing import StandardScaler
from threading import Lock
from sklearn.metrics import accuracy_score, precision_score, recall_score
from concurrent.futures import ThreadPoolExecutor
from telegram.error import NetworkError
from sklearn.model_selection import train_test_split, GridSearchCV, TimeSeriesSplit
from collections import OrderedDict
# تحميل المتغيرات البيئية
load_dotenv()

# الأفضل إضافتها في بداية الملف بعد الواردات
class APIError(Exception):
    def __init__(self, message, status_code=None):
        self.status_code = status_code
        super().__init__(message)

class APIConnectionError(Exception):
    def __init__(self, message, original_exception=None):
        self.original = original_exception
        super().__init__(f"{message}: {str(original_exception)}")

class APITimeoutError(APIError):
    """مهلة طلب API"""

class BinanceAPIError(APIError):
    """خطأ من Binance API"""
    
class InsufficientFundsError(APIError):
    """رصيد غير كافي"""
    
class InvalidResponseError(APIError):
    """استجابة غير صالحة"""
    
class TradingBot:
    def __init__(self):
        # تهيئة جميع السمات الأساسية أولاً
        self.lock = Lock()
        self.is_running = False
        self.start_time = None
        self.current_positions = {}
        self.symbols = ["ADAUSDT", "XLMUSDT", "ALGOUSDT"]
        self.models = {}
        self.news_sources = ["telegram", "twitter", "coindesk", "cryptopanic", "newsapi"]
        self.rotation_index = 0
        self.last_api_call = {}
        self._model_cache = OrderedDict()
        self._max_cached_models = 3
        self.news_rotation_indices = {symbol: 0 for symbol in self.symbols}
        self.news_fetch_interval_hours = 12
        self.last_news_fetch_time = datetime.min
        self.optimal_trading_hours = []
        self._news_cache = {}

        # تهيئة القواميس الخاصة بالتحليل والإشارات
        self.news_sentiment = {
            symbol: {
                "score": 0,
                "positive": 0,
                "negative": 0,
                "neutral": 0,
                "last_updated": None,
                "source": None
            } for symbol in self.symbols
        }

        self.pro_signals = {symbol: [] for symbol in self.symbols}
        self.trailing_stops = {symbol: None for symbol in self.symbols}
        self.last_peaks = {symbol: None for symbol in self.symbols}
        self.fib_levels = {symbol: None for symbol in self.symbols}
        self.pivot_points = {symbol: None for symbol in self.symbols}

        # إعدادات التداول
        self.min_profit = 0.4
        self.trailing_percent = 0.1
        self.min_expected_profit = 0.6  

        # تهيئة نظام التسجيل
        self._init_logging()

        # تهيئة APIs
        try:
            self.client = Client(os.getenv('BINANCE_API_KEY'), os.getenv('BINANCE_SECRET_KEY'))
            self.tg_bot = Bot(token=os.getenv('TELEGRAM_TOKEN'))
        except Exception as e:
            self.logger.critical("فشل تهيئة APIs - الخطأ: %s", str(e), exc_info=True)
            self.send_notification(
                'error',
                f"🔥 فشل حرج في تهيئة APIs\n"
                f"📛 التفاصيل: {str(e)}\n"
                f"⏰ الوقت: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
            )
            self.shutdown_bot(reason=f"فشل تهيئة APIs: {str(e)}")
            raise RuntimeError(f"فشل تهيئة APIs - تم إيقاف البوت. الخطأ الأصلي: {str(e)}") from e

        # تحميل الحالة العامة والمؤشرات
        self.load_state()
        self.load_rotation_index()

        # تحميل النماذج لكل عملة مع نظام طوارئ متكامل
        self.models = {}
        for symbol in self.symbols:
            try:
                # 1. محاولة تحميل النموذج الرئيسي
                model = self.load_or_initialize_model(symbol, use_cache=True)
                
                # 2. التحقق من صحة النموذج
                if model is None:
                    raise ValueError("النموذج غير محمل (قيمة None)")
                
                # 3. اختبار عملي للنموذج
                test_data = pd.DataFrame([[
                    0, 0, 50, 0, 1000000, 0, 0
                ]], columns=[
                    'ema20', 'ema50', 'rsi', 'macd',
                    'volume', 'news_sentiment', 'signal_count'
                ])
                
                prediction = model.predict(test_data)
                if prediction is None or len(prediction) == 0:
                    raise ValueError("فشل في توليد التنبؤات")
                
                # 4. إذا نجحت جميع الاختبارات
                self.models[symbol] = model
                self.logger.info("تم تحميل النموذج بنجاح لـ %s", symbol)
                
            except Exception as e:
                self.logger.error("فشل تحميل النموذج الرئيسي لـ %s: %s", symbol, str(e), exc_info=True)
                
                try:
                    # 5. محاولة تحميل نسخة احتياطية
                    backup_model = self._load_backup_model(symbol)
                    if backup_model:
                        self.models[symbol] = backup_model
                        self.logger.warning("تم تحميل نسخة احتياطية لـ %s", symbol)
                        continue
                        
                    # 6. إنشاء نموذج طوارئ بسيط
                    self.models[symbol] = self._create_emergency_model()
                    self.logger.critical("تم إنشاء نموذج طوارئ لـ %s", symbol)
                    
                    self.send_notification(
                           'warning',
                           f"⚠️ تحذير: تم استخدام نموذج طوارئ لـ {symbol}\nالسبب: {str(e)[:150]}"
                     )
                    
                except Exception as emergency_error:
                    self.logger.critical(
                        "فشل إنشاء نموذج طوارئ لـ %s: %s",
                        symbol, str(emergency_error),
                        exc_info=True
                    )
                    self.shutdown_bot(reason=f"فشل حرج في تحميل النماذج: {str(emergency_error)}")
                    raise RuntimeError(f"لا يمكن المتابعة بدون نموذج لـ {symbol}") from emergency_error

    def initialize_fallback_model(self):
        """إنشاء نموذج بديل أساسي في حال فشل التحميل"""
        try:
            model = Pipeline([
                ('scaler', StandardScaler()),
                ('xgb', XGBClassifier(
                    objective='binary:logistic',
                    learning_rate=0.05,
                    max_depth=3,
                    n_estimators=100,
                    random_state=42
                ))
            ])
            
            # إنشاء بيانات تدريب وهمية أساسية
            dummy_X = pd.DataFrame(np.random.rand(10, 7), columns=[
                'ema20', 'ema50', 'rsi', 'macd',
                'volume', 'news_sentiment', 'signal_count'
            ])
            dummy_y = np.random.randint(0, 2, 10)
            
            # تدريب سريع على بيانات وهمية
            model.fit(dummy_X, dummy_y)
            
            return model
            
        except Exception as e:
            self.logger.error("فشل إنشاء نموذج بديل: %s", str(e), exc_info=True)
            raise RuntimeError("لا يمكن إنشاء نموذج بديل") from e

    def _init_logging(self):
        """إعداد نظام تسجيل الأخطاء الآمن مع تجنب التعارض في الملفات"""
        try:
            # 1. إنشاء مجلد اللوجات إذا لم يكن موجوداً
            logs_dir = 'logs'
            os.makedirs(logs_dir, exist_ok=True)

            # 2. إنشاء اسم فريد لل logger مع تجنب التعارض
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            logger_name = f'trading_bot_{timestamp}'
            
            # 3. التحقق من عدم وجود ملف بنفس الاسم (حماية إضافية)
            log_file = f'{logs_dir}/bot_{datetime.now().strftime("%Y%m%d")}.log'
            counter = 1
            while os.path.exists(log_file):
                log_file = f'{logs_dir}/bot_{datetime.now().strftime("%Y%m%d")}_{counter}.log'
                counter += 1

            # 4. إنشاء logger جديد
            self.logger = logging.getLogger(logger_name)
            self.logger.setLevel(logging.DEBUG)

            # 5. منع تكرار ال handlers
            if self.logger.hasHandlers():
                self.logger.handlers.clear()

            # 6. إنشاء formatter متقدم
            formatter = logging.Formatter(
                '%(asctime)s | %(levelname)-8s | %(name)s | %(message)s | Line:%(lineno)d',
                datefmt='%Y-%m-%d %H:%M:%S'
            )

            # 7. إنشاء file handler مع تدوير الملفات
            file_handler = RotatingFileHandler(
                log_file,
                maxBytes=5*1024*1024,  # 5MB
                backupCount=3,
                encoding='utf-8'
            )
            file_handler.setFormatter(formatter)
            self.logger.addHandler(file_handler)

            # 8. إنشاء console handler للطوارئ
            console_handler = logging.StreamHandler()
            console_handler.setFormatter(formatter)
            self.logger.addHandler(console_handler)

            # 9. تسجيل بدء التشغيل
            self.logger.info("✅ تم تهيئة نظام التسجيل بنجاح")

        except Exception as e:
          #نظام الطوارئ عند فشل تهيئة نظام التسجيل
            try:
                # أ. تهيئة أساسيات logging
                logging.basicConfig(
                    level=logging.DEBUG,
                    format='%(asctime)s - EMERGENCY - %(message)s',
                    handlers=[
                        logging.StreamHandler(),  # إخراج إلى الكونسول
                        logging.FileHandler('emergency.log')  # ملف طوارئ منفصل
                    ]
                )

                # ب. إنشاء logger الطوارئ
                emergency_logger = logging.getLogger('EMERGENCY_LOGGER')
                emergency_logger.setLevel(logging.DEBUG)

                # ج. تسجيل التفاصيل الكاملة للخطأ
                emergency_logger.critical("فشل تهيئة نظام التسجيل الرئيسي | الخطأ: %s", str(e), exc_info=True)
                # د. تعيين logger الطوارئ للنظام
                self.logger = emergency_logger

            except Exception as nested_ex:
                # أبسط حل كحماية أخيرة
                with open('crash_report.log', 'a', encoding='utf-8') as f:
                    f.write(f"[{datetime.now()}] SYSTEM COLLAPSE: {str(e)}\n")
                    f.write(f"[{datetime.now()}] EMERGENCY FAILURE: {str(nested_ex)}\n")
        
    def _clean_model_cache(self):
        while len(self._model_cache) > self._max_cached_models:
            symbol, _ = self._model_cache.popitem(last=False)
            print(f"تمت إزالة: {symbol} (الحجم الآن: {len(self._model_cache)})")
            
    def add_model(self, symbol, model):
        self._model_cache[symbol] = model
        self._clean_model_cache()

    def _safe_load_model(self, path):
        """نسخة محسنة مع ضمانات إضافية"""
        try:
            # 1. تحقق من وجود الملف
            if not os.path.exists(path):
                raise FileNotFoundError(f"الملف غير موجود: {path}")

            # 2. تحقق من الحجم
            if os.path.getsize(path) == 0:
                raise ValueError("ملف النموذج فارغ")

            # 3. تحميل النموذج
            with open(path, 'rb') as f:
                model = joblib.load(f)

            # 4. التحقق من وجود الدوال المطلوبة
            required_methods = ['predict', 'fit']
            for method in required_methods:
                if not hasattr(model, method):
                    raise AttributeError(f"النموذج يفتقد إلى: {method}")

            # 5. إصدار sklearn
            if hasattr(model, '__sklearn_version__'):
                current_version = sklearn.__version__
                model_version = model.__sklearn_version__
                if model_version != current_version:
                    self.logger.warning("⚠️ إصدار sklearn غير متطابق (النموذج: %s، الحالي: %s)", model_version, current_version)

            return model

        except Exception as e:
            # 6. نقل الملف التالف
            try:
                corrupt_path = f"{path}.corrupt_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
                shutil.move(path, corrupt_path)
                self.logger.error("تم نقل النموذج التالف إلى: %s", corrupt_path)
            except Exception as move_error:
                self.logger.error("فشل نقل الملف التالف: %s", str(move_error))

            self.send_notification(
                'error',
                f"❌ نموذج تالف\n"
                f"📂 {os.path.basename(path)}\n"
                f"📛 {type(e).__name__}: {str(e)[:100]}"
            )
            return None

    def _validate_news_sources(self):
        """التحقق من صحة مصادر الأخبار مع ضمانات كاملة ودعم 5 مصادر"""
        VALID_SOURCES = {
            'telegram', 'twitter', 'coindesk', 
            'cryptopanic', 'newsapi'
        }

        DEFAULT_SOURCES = [
            'telegram', 'twitter', 'coindesk', 
            'cryptopanic', 'newsapi'
        ]

        try:
            if not hasattr(self, 'news_sources'):
                self.news_sources = DEFAULT_SOURCES.copy()
                self._log_reset("لم يتم تعريف مصادر الأخبار")
                return

            fixed_sources = []
            problems = []

            for src in self.news_sources:
                clean_src = str(src).strip().lower() if src else ''
                
                if not clean_src:
                    problems.append(f"مصدر فارغ: {src}")
                    continue
                    
                if clean_src not in VALID_SOURCES:
                    problems.append(f"مصدر غير معتمد: {clean_src}")
                    continue
                    
                fixed_sources.append(clean_src)

            if problems:
                self.logger.warning("مشاكل في المصادر: %s", ', '.join(problems))

            if not fixed_sources:
                self.news_sources = DEFAULT_SOURCES.copy()
                self._log_reset("لا توجد مصادر صالحة بعد التصفية")
            else:
                self.news_sources = list(dict.fromkeys(fixed_sources))
                
                for essential in ['twitter', 'telegram']:
                    if essential not in self.news_sources:
                        self.news_sources.append(essential)
                        self.logger.info("أضيف مصدر أساسي: %s", essential)

        except Exception as e:
            self.logger.critical("فشل التحقق من المصادر: %s", str(e), exc_info=True)
            self.news_sources = DEFAULT_SOURCES.copy()

    def _log_reset(self, reason):
        """تسجيل تفاصيل إعادة التعيين"""
        msg = f"تم ضبط مصادر الأخبار. السبب: {reason} | المصادر الجديدة: {self.news_sources}"
        self.logger.warning("%s", msg)
        self.send_notification('config_update', msg)

    def collect_market_data(self, symbol):  # <-- الدالة المعدّلة
        """
        جمع البيانات السعرية لعملة محددة مع التحليل الفني
        
        Parameters:
            symbol (str): رمز العملة (مثل 'ADAUSDT').
        
        Returns:
            DataFrame: بيانات الأسعار مع المؤشرات الفنية أو None إذا فشل.
        """
        try:
            df = self.get_historical_data(symbol)
            if df is None or df.empty:
                raise ValueError("⚠️ البيانات التاريخية غير متاحة أو فارغة")
            
            df = self.calculate_technical_indicators(df)
            return df

        except requests.exceptions.RequestException as e:
            self.send_notification('connection', f'🌐 فشل في الاتصال بالشبكة: {e}')
            return None

        except Exception as e:
            self.send_notification('error', f'❌ فشل غير متوقع: {type(e).__name__}: {e}')
            return None

    def fetch_signals_for_symbol(self, symbol):
        """
        جلب الإشارات الاحترافية لعملة محددة من مصادر متعددة

        Args:
            symbol (str): رمز العملة (مثل 'ADAUSDT')

        Returns:
            list: قائمة بالإشارات مع تفاصيل كل إشارة
        """
        signals = []

        try:
            # 1. جلب إشارات التويتر
            twitter_signals = self._fetch_twitter_signals(symbol)
            signals.extend(twitter_signals)

            # 2. جلب إشارات التليجرام
            telegram_signals = self._fetch_telegram_signals(symbol)
            signals.extend(telegram_signals)

            # 3. جلب إشارات من مصادر أخرى
            other_signals = self._fetch_other_sources(symbol)
            signals.extend(other_signals)

        except Exception as e:
            self.logger.error("فشل جلب الإشارات لـ %s: %s", symbol, str(e), exc_info=True)
            self.send_notification('error', f"❌ فشل جلب إشارات {symbol}")

        return signals

    def get_latest_crypto_news(self, symbol, hours=48):
        """
        جمع أحدث أخبار الكريبتو من مصادر متعددة خلال الساعات المحددة لرمز معين
        """
        news_items = []
        cutoff_time = datetime.now() - timedelta(hours=hours)

        # 1. أخبار من تويتر
        try:
            twitter_news = self._fetch_twitter_news(hours)
            if twitter_news:
                news_items.extend([
                    item for item in twitter_news 
                    if datetime.fromisoformat(item['time']) > cutoff_time
                ])
        except Exception as e:
            self.logger.error("فشل جلب أخبار تويتر: %s", str(e))

        # 2. أخبار من كوين ديسك
        try:
            coindesk_news = self.scrape_coindesk_news(symbol)
            if coindesk_news:
                news_items.extend([
                    item for item in coindesk_news 
                    if datetime.fromisoformat(item['time']) > cutoff_time
                ])
        except Exception as e:
            self.logger.error("فشل جلب أخبار كوين ديسك: %s", str(e))

        # 3. أخبار من كريبتو بانيك (تحليل معنويات فقط، لا توجد أخبار مفصلة)
        try:
            self.scrape_cryptopanic_news(symbol)  # لا ترجع أخبار
        except Exception as e:
            self.logger.error("فشل جلب أخبار كريبتو بانيك: %s", str(e))

        # 4. أخبار من تليجرام
        try:
            telegram_news = self.scrape_telegram_news()
            if telegram_news:
                news_items.extend([
                    item for item in telegram_news 
                    if datetime.fromisoformat(item['time']) > cutoff_time
                ])
        except Exception as e:
            self.logger.error("فشل جلب أخبار تليجرام: %s", str(e))

        # ترتيب الأخبار حسب الأحدث
        news_items.sort(key=lambda x: datetime.fromisoformat(x['time']), reverse=True)

        return news_items[:50]  # إرجاع آخر 50 خبر فقط

    def _fetch_twitter_signals(self, symbol):
        """نسخة محسنة من دالة جلب إشارات التويتر بتحليل لغوي متقدم"""
        signals = []
        coin_name = symbol[:-4]  # إزالة USDT
        cutoff_time = datetime.now() - timedelta(hours=48)
        trusted_sources = ['CryptoMichNL', 'Ali_Charts', 'rektcapital', 'CryptoTony__', 'TheCryptoDog']
        
        for username in trusted_sources:
            try:
                tweets = self._get_user_tweets(username)
                for tweet in tweets:
                    try:
                        tweet_time = self._safe_parse_date(tweet.get('created_at', ''))
                        if tweet_time is None or tweet_time < cutoff_time:
                            continue
                            
                        tweet_text = tweet.get('text', '').lower()
                        
                        # 1. التحقق من ذكر العملة
                        if coin_name.lower() not in tweet_text:
                            continue
                            
                        # 2. تحليل المشاعر المتقدم
                        sentiment = self._advanced_sentiment_analysis(tweet_text)
                        
                        # 3. الكشف عن الإشارات الضمنية
                        signal_type = self._detect_signal_type(tweet_text)
                        
                        if signal_type != 'neutral':
                            signals.append({
                                'source': 'Twitter',
                                'author': username,
                                'text': tweet.get('text', '')[:200],
                                'time': tweet_time.isoformat(),
                                'sentiment': sentiment,
                                'signal_type': signal_type,
                                'confidence': self._calculate_confidence(tweet_text)
                            })
                    except Exception as tweet_error:
                        self.logger.warning("خطأ في معالجة تغريدة من %s: %s", username, str(tweet_error))
                        continue
                        
            except Exception as e:
                self.logger.warning("فشل معالجة تغريدات %s: %s", username, str(e))
                continue

        return signals

    @staticmethod
    def _advanced_sentiment_analysis(text):
        """تحليل مشاعر متقدم باستخدام TextBlob مع تحسينات"""
        analysis = TextBlob(text)
        
        # تحسين تحليل المشاعر للسياق المالي
        financial_words = {
            'bullish': 0.8,
            'bearish': -0.8,
            'pump': -0.5,
            'dump': -0.7,
            'moon': 0.9,
            'rocket': 0.7,
            'crash': -0.9,
            'rally': 0.6
        }
        
        # تعديل النتيجة بناء على المصطلحات المالية
        for word, weight in financial_words.items():
            if word in text:
                # نعدل القيمة بحيث تبقى بين -1 و1
                analysis.sentiment = analysis.sentiment._replace(
                    polarity=min(1.0, max(-1.0, analysis.sentiment.polarity + weight * 0.3))
                )
        
        return round(analysis.sentiment.polarity, 2)

    @staticmethod
    def _detect_signal_type(text):
        """الكشف عن نوع الإشارة باستخدام تحليل سياقي"""
        text = text.lower()
        
        # قوائم الكلمات الدالة
        buy_signals = ['buy', 'long', 'bullish', 'accumulate', 'entry', 'moon', 'rocket']
        sell_signals = ['sell', 'short', 'bearish', 'exit', 'dump', 'crash']
        caution_signals = ['warning', 'caution', 'careful', 'volatile']
        
        # تحليل النص
        buy_count = sum(text.count(word) for word in buy_signals)
        sell_count = sum(text.count(word) for word in sell_signals)
        caution_count = sum(text.count(word) for word in caution_signals)
        
        # تحديد نوع الإشارة
        if buy_count > sell_count and buy_count > caution_count:
            return 'buy'
        elif sell_count > buy_count and sell_count > caution_count:
            return 'sell'
        elif caution_count > max(buy_count, sell_count):
            return 'caution'
        else:
            return 'neutral'

    @staticmethod
    def _calculate_confidence(text):
        """حساب ثقة الإشارة بناء على عوامل متعددة"""
        factors = []

        # 1. طول التغريدة
        factors.append(min(1.0, len(text) / 100))

        # 2. عدد المصطلحات الدالة
        keywords = ['target', 'stop', 'resistance', 'support', 'breakout']
        factors.append(min(1.0, sum(text.count(kw) for kw in keywords) / 3))

        # 3. علامات الترقيم (العلامات القوية)
        strong_punct = ['!', '🚀', '🔥', '📈', '📉']
        factors.append(min(1.0, sum(text.count(p) for p in strong_punct) / 2))

        # متوسط عوامل الثقة
        return round(sum(factors) / len(factors), 2)

    def _safe_parse_date(self, date_str):
        """تحويل التاريخ بشكل آمن مع دعم تنسيقات متعددة"""
        if not date_str:
            return None
            
        formats_to_try = [
            '%Y-%m-%dT%H:%M:%S.%fZ',  # التنسيق الأصلي
            '%Y-%m-%dT%H:%M:%SZ',     # تنسيق بدون أجزاء الثواني
            '%a %b %d %H:%M:%S %z %Y' # تنسيق آخر شائع في تويتر
        ]
        
        for fmt in formats_to_try:
            try:
                return datetime.strptime(date_str, fmt)
            except ValueError:
                continue
                
        self.logger.warning("فشل تحويل التاريخ: %s - لا يوجد تنسيق مطابق", date_str)
        return None

    def _fetch_twitter_news(self, hours=48):  # جعل hours=48 افتراضيًا
        query = "crypto OR cryptocurrency OR bitcoin OR ethereum -filter:retweets"
        tweets = self._search_twitter(query, count=50)
        cutoff_time = datetime.now() - timedelta(hours=hours)
        
        news = []
        for tweet in tweets:
            tweet_time = datetime.strptime(tweet['created_at'], '%Y-%m-%dT%H:%M:%S.%fZ')
            if tweet_time > cutoff_time:
                news.append({
                    'source': 'Twitter',
                    'author': tweet['user']['screen_name'],
                    'text': tweet['text'],
                    'time': tweet_time.isoformat(),
                    'sentiment': TextBlob(tweet['text']).sentiment.polarity
                })
        
        return news

    def get_all_twitter_data(self, symbol=None, hours=48):
        all_data = []
        
        # جلب الإشارات (إذا وُفر رمز العملة)
        if symbol:
            all_data.extend(self._fetch_twitter_signals(symbol))
        
        # جلب الأخبار العامة
        all_data.extend(self._fetch_twitter_news(hours))
        
        # إزالة التكرارات بناءً على نص التغريدة
        unique_data = {item['text']: item for item in all_data}.values()
        
        # ترتيب حسب الوقت (الأحدث أولاً)
        return sorted(unique_data, key=lambda x: x['time'], reverse=True)

    @staticmethod
    def _get_twitter_api_v2():
        """تهيئة اتصال Twitter API v2 باستخدام Bearer Token"""
        headers = {
            "Authorization": f"Bearer {os.getenv('TWITTER_BEARER_TOKEN')}",
            "User-Agent": "v2UserLookupPython"
        }
        return headers

    def _get_user_tweets(self, username, count=15):
        """
        جلب تغريدات مستخدم معين باستخدام Twitter API v2
        
        Args:
            username (str): اسم المستخدم في تويتر
            count (int): عدد التغريدات المطلوبة (افتراضي 15)
        
        Returns:
            list: قائمة تغريدات تحتوي على النص والتاريخ والمستخدم
        """
        try:
            headers = self._get_twitter_api_v2()
            if not headers:
                return []

            # الحصول على ID المستخدم
            user_url = f"https://api.twitter.com/2/users/by/username/{username}"
            user_response = requests.get(user_url, headers=headers)
            user_data = user_response.json()

            if 'data' not in user_data:
                return []

            user_id = user_data['data']['id']

            # جلب التغريدات
            tweets_url = f"https://api.twitter.com/2/users/{user_id}/tweets"
            params = {
                'max_results': count,
                'exclude': 'replies,retweets',
                'tweet.fields': 'created_at,text'
            }

            tweets_response = requests.get(tweets_url, headers=headers, params=params)
            tweets_data = tweets_response.json()

            return [{
                'text': tweet['text'],
                'created_at': tweet['created_at'],
                'user': {
                    'username': username,
                    'id': user_id
                }
            } for tweet in tweets_data.get('data', [])]

        except Exception as e:
            self.logger.error("فشل جلب تغريدات %s: %s", username, str(e))
            return []

    def _fetch_telegram_signals(self, symbol):
        """جلب إشارات التداول من قنوات التليجرام المخصصة"""
        signals = []
        coin_name = symbol[:-4]  # إزالة USDT

        try:
            channels = [
                'CryptoSignalsIO',
                'BinanceSignalsOfficial',
                'UniversalCryptoSignals'
            ]

            api_id = int(os.getenv('TG_API_ID'))
            api_hash = os.getenv('TG_API_HASH')

            with TelegramClient('session_name', api_id, api_hash) as client:
                for channel in channels:
                    try:
                        messages = client.get_messages(channel, limit=20)

                        for msg in messages:
                            if not msg.text:
                                continue

                            if (coin_name.lower() in msg.text.lower() and
                                any(word in msg.text.lower()
                                    for word in ['buy', 'long', 'bullish'])):

                                sentiment = TextBlob(msg.text).sentiment.polarity

                                signals.append({
                                    'source': 'Telegram',
                                    'channel': channel,
                                    'text': msg.text[:200],
                                    'time': msg.date.isoformat(),
                                    'sentiment': round(sentiment, 2)
                                })

                    except Exception as e:
                        self.logger.warning("فشل جلب رسائل %s: %s", channel, str(e))
                        continue

        except Exception as e:
            self.logger.error("فشل جلب إشارات التليجرام: %s", str(e), exc_info=True)
            raise

        return signals

    @staticmethod
    def _fetch_other_sources(symbol):
        """جلب إشارات من مصادر أخرى (مثل منتديات، مواقع متخصصة)"""
        signals = []

        # يمكن إضافة مصادر أخرى هنا
        # مثل: TradingView, CoinMarketCap, etc.

        return signals

    def start_scheduler(self):
        """
        بدء الجدولة بأقل تعقيد ممكن
        """
        if self.is_running:
            return  # إذا كانت تعمل لا نعيد تشغيلها

        self.is_running = True

        def scheduler_loop():
            last_optimization = None
            while self.is_running:  # الشرط الجديد
                try:
                    schedule.run_pending()

                    # التحسين الأسبوعي (يبقى كما هو)
                    now = datetime.now()
                    if now.weekday() == 6 and now.hour == 2 and (
                        last_optimization is None or (now - last_optimization).days >= 7
                    ):
                        self._run_weekly_optimization()
                        last_optimization = now

                    time.sleep(1)

                except Exception as e:
                    self.logger.error("خطأ في الجدولة: %s", e)
                    time.sleep(5)

        # تشغيل الثريد
        threading.Thread(
            target=scheduler_loop,
            daemon=True
        ).start()

    def _run_weekly_optimization(self):
        """تنفيذ التحسين الأسبوعي لجميع الرموز مع معالجة الأخطاء"""
        self.logger.info("بدء عملية التحسين الأسبوعي")
        for symbol in self.symbols:
            try:
                self.optimize_entry_conditions(symbol)
            except Exception as sym_error:
                self.logger.error("فشل تحسين %s: %s", symbol, str(sym_error), exc_info=True)
        self.logger.info("اكتمال عملية التحسين الأسبوعي")
    
    def analyze_news_sentiment(self, symbol=None):
        """
        تحليل مشاعر الأخبار مع ضمانات عدم الفشل
        Args:
            symbol: رمز العملة (اختياري) إذا كان التحليل خاصًا بعملة محددة
        Returns:
            float: درجة المشاعر بين -1 (سلبية) و +1 (إيجابية)
        """
        total_score = 0.0
        count = 0

        try:
            # 1. أخبار من NewsAPI
            if 'newsapi' in self.news_sources:
                try:
                    url = f"https://newsapi.org/v2/everything?q={'Crypto' if not symbol else symbol[:-4]}&apiKey={os.getenv('NEWSAPI_KEY')}"
                    response = requests.get(url, timeout=10)
                    articles = response.json().get('articles', [])

                    for article in articles[:5]:
                        content = f"{article.get('title', '')}. {article.get('description', '')}"
                        if content.strip():
                            sentiment = TextBlob(content).sentiment.polarity
                            total_score += sentiment
                            count += 1
                except Exception as e:
                    self.logger.error("NewsAPI Error: %s", str(e), exc_info=True)

            # 2. أخبار من CryptoPanic
            if 'cryptopanic' in self.news_sources:
                try:
                    coin_symbol = symbol[:-4] if symbol else 'BTC'
                    url = f"https://cryptopanic.com/api/v1/posts/?auth_token={os.getenv('CRYPTO_PANIC_KEY')}&currencies={coin_symbol}"
                    response = requests.get(url, timeout=10)
                    posts = response.json().get('results', [])

                    for post in posts[:5]:
                        content = f"{post.get('title', '')}. {post.get('body', '')}"
                        if content.strip():
                            sentiment = TextBlob(content).sentiment.polarity
                            total_score += sentiment
                            count += 1
                except Exception as e:
                    self.logger.error("CryptoPanic Error: %s", str(e), exc_info=True)

            # 3. حساب النتيجة النهائية
            final_score = total_score / max(1, count)

            # 4. تحديث حالة الأخبار إذا وُجد رمز
            if symbol:
                self.news_sentiment[symbol] = {
                    'score': round(final_score, 4),
                    'positive': sum(1 for _ in range(count) if _ > 0.1),
                    'negative': sum(1 for _ in range(count) if _ < -0.1),
                    'neutral': sum(1 for _ in range(count) if -0.1 <= _ <= 0.1),
                    'last_updated': datetime.utcnow().isoformat(),
                    'source': 'combined'
                }

            return round(final_score, 4)

        except Exception as e:
            self.logger.critical("Total Sentiment Analysis Failure: %s", str(e), exc_info=True)
            return 0.0

    def scrape_cryptopanic_news(self, symbol, cache_hours=4):
        """
        نسخة محسنة مع تخزين مؤقت للنتائج
        """
        cache_key = f"cryptopanic_{symbol}"
        cached_data = self._get_cached_news(cache_key, cache_hours)
        
        if cached_data:
            self.news_sentiment[symbol] = cached_data
            return cached_data  # أضفت return هنا لإرجاع البيانات المخبأة
            
        try:
            coin_symbol = symbol[:-4].upper()
            trusted_sources = "coindesk,cointelegraph,decrypt"  # مصادر موثوقة (كما يدرجها CryptoPanic)
            url = f"https://cryptopanic.com/api/v1/posts/?auth_token={os.getenv('CRYPTO_PANIC_KEY')}&currencies={coin_symbol}&sources={trusted_sources}&kind=news"
            
            params = {
                'auth_token': os.getenv('CRYPTO_PANIC_KEY'),
                'currencies': coin_symbol,
                'public': 'true',
                'kind': 'news'
            }
            
            response = requests.get(url, params=params, timeout=15)
            data = response.json()
            
            with ThreadPoolExecutor(max_workers=3) as executor:
                futures = [executor.submit(self._analyze_cryptopanic_post, post) for post in data.get('results', [])[:5]]
                results = [f.result() for f in futures if f.result() is not None]
            
            if not results:
                return []  # أرجع قائمة فارغة بدل None
                
            avg_score = sum(r['sentiment'] for r in results) / len(results)
            positive = sum(1 for r in results if r['sentiment'] > 0.1)
            negative = sum(1 for r in results if r['sentiment'] < -0.1)
            neutral = len(results) - positive - negative
            
            sentiment_data = {
                "score": avg_score,
                "positive": positive,
                "negative": negative,
                "neutral": neutral,
                "last_updated": datetime.utcnow().isoformat(),
                "source": "cryptopanic"
            }
            
            self.news_sentiment[symbol] = sentiment_data
            self._cache_news(cache_key, sentiment_data)
            
            return results  # أضفت return هنا لإرجاع الأخبار المعالجة
            
        except Exception as e:
            self.send_notification('error', f'CryptoPanic Error: {str(e)}')
            return []  # أرجع قائمة فارغة في حالة الخطأ

    @staticmethod
    def _analyze_cryptopanic_post(post):
        """تحليل مقالة فردية من CryptoPanic"""
        try:
            title = post.get('title', '')
            body = post.get('body', '')
            
            if not title and not body:
                return None
                
            sentiment = TextBlob(f"{title}. {body}").sentiment.polarity
            return {
                'title': title,
                'sentiment': sentiment
            }
        except Exception:
            return None

    def scrape_newsapi_news(self, symbol):
        try:
            coin_name = symbol[:-4]  # إزالة USDT
            trusted_sources = "cointelegraph.com,decrypt.co,coindesk.com"  # مصادر موثوقة
            url = f"https://newsapi.org/v2/everything?q={coin_name}&domains={trusted_sources}&apiKey={os.getenv('NEWSAPI_KEY')}"
            response = requests.get(url)
            articles = response.json().get('articles', [])
            
            total_score = 0
            analyzed_articles = 0
            sentiments = []

            for article in articles[:5]:  # تحليل 5 مقالات فقط
                title = article.get('title', '')
                content = article.get('description', '') or article.get('content', '')
                
                if not content:
                    continue
                    
                sentiment = TextBlob(f"{title}. {content}").sentiment.polarity
                sentiments.append(sentiment)
                total_score += sentiment
                analyzed_articles += 1
            
            if analyzed_articles > 0:
                avg_score = total_score / analyzed_articles
                positive = sum(1 for s in sentiments if s > 0.1)
                negative = sum(1 for s in sentiments if s < -0.1)
                neutral = analyzed_articles - positive - negative

                self.news_sentiment[symbol] = {
                    "score": avg_score,
                    "positive": positive,
                    "negative": negative,
                    "neutral": neutral,
                    "last_updated": datetime.utcnow().isoformat(),
                    "source": "newsapi"
                }
                
        except Exception as e:
            self.send_notification('error', f'❌ فشل تحليل NewsAPI: {e}')

    def scrape_coindesk_news(self, symbol, max_articles=5, cache_hours=6):
        """
        نسخة محسنة مع تخزين مؤقت ومعالجة متوازية
        """
        try:
            # التحقق من التخزين المؤقت أولاً
            cache_key = f"coindesk_{symbol}"
            cached_data = self._get_cached_news(cache_key, cache_hours)
            
            if cached_data:
                self.news_sentiment[symbol] = cached_data
                return []  # ← رجوع قائمة فارغة عند وجود كاش فقط

            coin_name = symbol[:-4]
            coin_mapping = {
                "ADA": "cardano",
                "XLM": "stellar",
                "ALGO": "algorand",
            }
            
            search_term = coin_mapping.get(coin_name, coin_name.lower())
            trusted_authors = ['omkar-godbole', 'jessica-aznar', 'sam-reynolds']  # كتّاب CoinDesk الموثوقين
            url = f"https://www.coindesk.com/search?s={search_term}&author={','.join(trusted_authors)}"
            
            headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}
            
            response = requests.get(url, headers=headers, timeout=15)
            response.raise_for_status()
            
            soup = BeautifulSoup(response.text, 'html.parser')
            articles = soup.find_all('div', class_='article-cardstyles__StyledWrapper-q1x8lc-0')[:max_articles]
            
            if not articles:
                return []  # ← لا توجد مقالات، رجّع قائمة فارغة
            
            # معالجة المقالات بشكل متوازي
            with ThreadPoolExecutor(max_workers=3) as executor:
                futures = [executor.submit(self._process_coindesk_article, article) for article in articles]
                results = [f.result() for f in futures if f.result() is not None]
            
            if not results:
                return []  # ← لا نتائج مفيدة، رجّع قائمة فارغة

            total_score = sum(r['sentiment'] for r in results)
            avg_score = total_score / len(results)
            
            sentiment_data = {
                "score": avg_score,
                "positive": sum(1 for r in results if r['sentiment'] > 0.1),
                "negative": sum(1 for r in results if r['sentiment'] < -0.1),
                "neutral": sum(1 for r in results if -0.1 <= r['sentiment'] <= 0.1),
                "last_updated": datetime.utcnow().isoformat(),
                "source": "coindesk"
            }
            
            self.news_sentiment[symbol] = sentiment_data
            self._cache_news(cache_key, sentiment_data)
            
            return results  # ← أهم شيء: رجع النتائج

        except Exception as e:
            self.send_notification('error', f'Coindesk Error: {str(e)}')
            return []  # ← عند الخطأ رجع قائمة فارغة

    @staticmethod
    def _process_coindesk_article(article):
        """معالجة مقالة فردية من Coindesk"""
        try:
            title = article.find('h6').text.strip()
            link = article.find('a')['href']
            
            if not link.startswith('http'):
                link = f"https://www.coindesk.com{link}"
                
            # جلب المحتوى مع مهلة قصيرة
            article_response = requests.get(link, timeout=8)
            article_soup = BeautifulSoup(article_response.text, 'html.parser')
            
            content_div = article_soup.find('div', class_='at-content-wrapper')
            if not content_div:
                return None
                
            content = ' '.join(p.text for p in content_div.find_all('p'))
            sentiment = TextBlob(f"{title}. {content}").sentiment.polarity
            
            return {
                'title': title,
                'link': link,
                'sentiment': sentiment
            }
            
        except Exception:
            return None

    def _get_cached_news(self, key, max_hours):
        """استرجاع البيانات المخزنة مؤقتًا إذا كانت حديثة"""
        cached = self._news_cache.get(key)
        if cached:
            last_updated = datetime.fromisoformat(cached['last_updated'])
            if (datetime.utcnow() - last_updated) < timedelta(hours=max_hours):
                return cached
        return None

    def _cache_news(self, key, data):
        """تخزين البيانات مؤقتًا"""
        self._news_cache[key] = data

    def scrape_twitter_news(self, symbol=None):
        """
        جمع أخبار من تويتر مع ضمانات عدم الفشل
        
        Args:
            symbol (str|None): رمز العملة (مثل ADAUSDT) أو None للبحث العام
        
        Returns:
            list: قائمة بالأخبار المستخرجة مع التحليل
        """
        try:
            headers = {
                "Authorization": f"Bearer {os.getenv('TWITTER_BEARER_TOKEN')}",
                "User-Agent": "v2TweetLookupPython"
            }

            query = f"#{symbol[:-4]} crypto" if symbol else "crypto news"
            
            # التحقق الأساسي قبل الإرسال
            if not query.strip():
                self.logger.warning("بحث تويتر فارغ")
                return []

            search_url = "https://api.twitter.com/2/tweets/search/recent"
            params = {
                'query': query + ' -is:retweet -is:reply',
                'max_results': 15,
                'tweet.fields': 'created_at,text,author_id',
                'expansions': 'author_id',
                'user.fields': 'username'
            }

            response = requests.get(search_url, headers=headers, params=params)
            response.raise_for_status()  # تأكيد نجاح الاتصال

            data = response.json()

            # التحقق من وجود البيانات الأساسية
            if 'data' not in data or not isinstance(data['data'], list):
                self.logger.warning("لا توجد تغريدات لـ %s", query)
                return []

            # ربط المعرفات بالأسماء
            users = {}
            if 'includes' in data and 'users' in data['includes']:
                users = {u['id']: u['username'] for u in data['includes']['users']}

            news_items = []
            for tweet in data['data']:
                try:
                    author_id = tweet.get('author_id')
                    news_items.append({
                        'source': 'Twitter',
                        'author': users.get(author_id, f"user_{author_id}"),
                        'text': tweet.get('text', '')[:250],
                        'time': tweet.get('created_at', ''),
                        'sentiment': round(TextBlob(tweet.get('text', '')).sentiment.polarity, 2)
                    })
                except Exception as tweet_error:
                    self.logger.error("خطأ في معالجة التغريدة: %s", tweet_error)
                    continue

            return news_items

        except requests.exceptions.RequestException as e:
            self.logger.error("فشل الاتصال بموقع تويتر: %s", str(e))
            return []
        except Exception as e:
            self.logger.error("فشل غير متوقع: %s: %s", type(e).__name__, str(e))
            return []

    def _search_twitter(self, query, count=15):
        """
        بحث آمن في تويتر مع معالجة شاملة للأخطاء
        """
        try:
            headers = self._get_twitter_api_v2()
            if not headers:
                return []

            search_url = "https://api.twitter.com/2/tweets/search/recent"
            params = {
                'query': query,
                'max_results': count,
                'tweet.fields': 'created_at,author_id,text',
                'expansions': 'author_id',
                'user.fields': 'username,name'
            }

            response = requests.get(search_url, headers=headers, params=params)
            response.raise_for_status()

            data = response.json()

            # معالجة بيانات المستخدمين بشكل آمن
            users = {}
            if 'includes' in data and 'users' in data['includes']:
                try:
                    users = {
                        u['id']: {
                            'username': u.get('username', f"user_{u['id']}"),
                            'name': u.get('name', '')
                        }
                        for u in data['includes']['users']
                    }
                except Exception as users_error:
                    self.logger.error("خطأ في معالجة بيانات المستخدمين: %s", str(users_error))

            # معالجة التغريدات بشكل آمن
            tweets = []
            if 'data' in data and isinstance(data['data'], list):
                for tweet in data['data']:
                    try:
                        author_info = users.get(tweet.get('author_id'), {})
                        tweets.append({
                            'text': tweet.get('text', '')[:250],  # تقليل حجم النص
                            'created_at': tweet.get('created_at', ''),
                            'user': {
                                'screen_name': author_info.get('username', 'unknown'),
                                'name': author_info.get('name', '')
                            }
                        })
                    except Exception as tweet_error:
                        self.logger.error("خطأ في معالجة التغريدة: %s", str(tweet_error))
                        continue

            return tweets

        except requests.exceptions.RequestException as e:
            self.logger.error("فشل الاتصال بموقع تويتر: %s", str(e))
            return []
        except Exception as e:
            self.logger.error("فشل غير متوقع: %s: %s", type(e).__name__, str(e))
            return []
    
    def scrape_telegram_news(self, symbol=None):
        """
        جمع الأخبار من قنوات التليجرام عن عملة محددة أو الكريبتو بشكل عام

        Args:
            symbol (str|None): رمز العملة أو None للعام

        Returns:
            dict: بيانات الأخبار المجمعة
        """
        news_items = []
        channels = [
            'CryptocurrencyNews',
            'CoinDesk',
            'CryptoSignals'
        ]
        
        try:
            api_id = int(os.getenv('TG_API_ID'))
            api_hash = os.getenv('TG_API_HASH')
            
            with TelegramClient('session_name', api_id, api_hash) as client:
                for channel in channels:
                    try:
                        # جلب آخر 20 رسالة من القناة
                        messages = client.get_messages(channel, limit=20)
                        
                        for msg in messages:
                            if not msg.text:
                                continue
                                
                            # إذا كان هناك عملة محددة، نتحقق من ذكرها
                            if symbol and symbol[:-4].upper() not in msg.text.upper():
                                continue
                                
                            # تحليل المشاعر
                            sentiment = TextBlob(msg.text).sentiment.polarity
                            
                            news_items.append({
                                'source': 'Telegram',
                                'channel': channel,
                                'text': msg.text[:250],  # تقليل حجم النص
                                'time': msg.date.isoformat(),
                                'sentiment': round(sentiment, 2)
                            })
                            
                    except Exception as e:
                        self.logger.warning("فشل جلب رسائل %s: %s", channel, str(e))
                        continue
                        
        except Exception as e:
            self.logger.error("فشل جلب أخبار التليجرام: %s", str(e), exc_info=True)
            self.send_notification('error', '❌ فشل جمع أخبار التليجرام')
        
        # تخزين النتائج إذا كانت هناك عملة محددة
        if symbol:
            self.news_sentiment[symbol] = {
                'source': 'telegram',
                'items': news_items,
                'last_updated': datetime.now().isoformat()
            }
        
        return news_items

    def rotate_data_sources(self):
        """
        تدوير مؤشر مصدر الأخبار كل 12 ساعة بحيث يتغير المصدر لكل العملات.
        يتم حفظ المؤشر ويتم إرسال إشعار.
        """
        try:
            self.rotation_index = (self.rotation_index + 1) % len(self.news_sources)
            self.save_rotation_index()
            self.send_notification('update', f"تم تدوير مصادر الأخبار. المصدر الحالي: {self.news_sources[self.rotation_index]}")
        except Exception as e:
            self.send_notification('error', f'❌ فشل تدوير مصادر الأخبار: {e}')

    def save_rotation_index(self):
        """
        حفظ قيمة rotation_index في ملف أو قاعدة بيانات بسيطة ليتم استرجاعها عند إعادة تشغيل البوت.
        """
        try:
            with open('rotation_index.json', 'w') as f:
                json.dump({'rotation_index': self.rotation_index}, f)
        except Exception as e:
            self.send_notification('error', f"❌ فشل حفظ مؤشر التدوير: {e}")

    def load_rotation_index(self):
        """
        تحميل قيمة rotation_index من الملف عند بدء تشغيل البوت.
        """
        try:
            if os.path.exists('rotation_index.json'):
                with open('rotation_index.json', 'r') as f:
                    data = json.load(f)
                    self.rotation_index = data.get('rotation_index', 0)
            else:
                self.rotation_index = 0
        except Exception as e:
            self.send_notification('error', f"❌ فشل تحميل مؤشر التدوير: {e}")
            self.rotation_index = 0

    @staticmethod
    def round_quantity(quantity, step_size, min_qty=1e-6):
        """
        تقريب الكمية للأسفل لأقرب مضاعف للـ step_size، والتحقق أنها ≥ minQty.
        """
        rounded_qty = float(np.floor(quantity / step_size) * step_size)
        return rounded_qty if rounded_qty >= min_qty else 0

    def get_trade_limits(self, symbol):
        """يرجع الحد الأدنى للكمية وحجم الخطوة"""
        info = self.client.get_symbol_info(symbol)
        for f in info['filters']:
            if f['filterType'] == 'LOT_SIZE':
                return float(f['stepSize']), float(f['minQty'])
        return (0.1, 0.001)  # قيم افتراضية إذا لم توجد

    def update_news_sentiment(self, symbol):
        """
        تحديث درجة معنويات الأخبار لعملة معينة.
        هذه الدالة تعتمد على analyze_news_sentiment التي يجب أن تُرجع رقمًا بين -1 و 1.
        """
        try:
            score = self.analyze_news_sentiment(symbol)  # تحتاج لتكون معرفة مسبقًا

            if not hasattr(self, 'news_sentiment') or not isinstance(self.news_sentiment, dict):
                self.news_sentiment = {}

            self.news_sentiment[symbol] = {"score": score}

        except Exception as e:
            self.send_notification('error', f'⚠️ فشل تحديث معنويات الأخبار لـ {symbol}: {e}')
            self.news_sentiment[symbol] = {"score": 0}  # القيمة الافتراضية

    def calculate_quantity(self, symbol, risk_percent=0.02):
        """حساب الكمية بشكل ديناميكي مع مراعاة الحدود"""
        try:
            # 1. الحصول على الرصيد والسعر
            balance = float(self.client.get_asset_balance('USDT')['free'])
            ticker = self.client.get_symbol_ticker(symbol=symbol)
            current_price = float(ticker['price'])
            
            # 2. حساب المبلغ المستثمر
            investment = balance * 0.3
            
            # 3. الحصول على حدود التداول
            step_size, min_qty = self.get_trade_limits(symbol)  # من دالتك السابقة
            
            # 4. حساب الكمية مع التقريب
            quantity = (investment / current_price) // step_size * step_size
            
            # 5. التحقق من الحد الأدنى
            return max(quantity, min_qty)
            
        except Exception as e:
            self.send_notification('error', f"فشل حساب الكمية لـ {symbol}: {str(e)}")
            return 0  # تجنب الأخطاء عند التنفيذ

    def update_pro_signals(self, symbol):
        """
        تحديث الإشارات الاحترافية لعملة معينة (مثل إشارات من Telegram أو تحليل داخلي).
        تعتمد على fetch_signals_for_symbol التي تُرجع قائمة إشارات.
        """
        try:
            signals = self.fetch_signals_for_symbol(symbol)  # تحتاج لتكون معرفة

            if not hasattr(self, 'pro_signals') or not isinstance(self.pro_signals, dict):
                self.pro_signals = {}

            self.pro_signals[symbol] = signals

        except Exception as e:
            self.send_notification('error', f'⚠️ فشل تحديث إشارات {symbol}: {e}')
            self.pro_signals[symbol] = []

    def generate_performance_report(self):
        """
        إنشاء تقرير أداء شامل للبوت مع تحليل تنبؤات جميع النماذج
        """
        try:
            report_data = {
                'timestamp': datetime.now().isoformat(),
                'models': {},
                'overall': {
                    'active_signals': 0,
                    'buy_signals': 0,
                    'neutral_signals': 0
                }
            }

            for symbol in self.symbols:
                model = self.models.get(symbol)
                if not model:
                    continue

                # إنشاء بيانات الإدخال (النسخة المعدلة)
                input_data = pd.DataFrame([[
                    0, 0, 50, 0, 1000000,
                    self.news_sentiment.get(symbol, {}).get('score', 0),
                    len(self.pro_signals.get(symbol, []))
                ]], columns=[
                    'ema20', 'ema50', 'rsi', 'macd',
                    'volume', 'news_sentiment', 'signal_count'
                ])

                # زيادة عدد الإشارات النشطة
                signal_count = len(self.pro_signals.get(symbol, []))
                report_data['overall']['active_signals'] += signal_count

                try:
                    prediction = self.safe_model_prediction(model, input_data)

                    if prediction is not None:
                        prediction_label = 'شراء' if prediction[0] == 1 else 'انتظار'
                        report_data['overall']['buy_signals' if prediction[0] == 1 else 'neutral_signals'] += 1
                    else:
                        prediction_label = 'غير متاح'

                    report_data['models'][symbol] = {
                        'prediction': prediction_label,
                        'sentiment_score': round(self.news_sentiment.get(symbol, {}).get('score', 0), 2),
                        'signal_count': signal_count,
                        'last_updated': datetime.now().strftime('%Y-%m-%d %H:%M')
                    }

                except Exception as e:
                    self.logger.error("فشل تحليل الأداء لـ %s: %s", symbol, str(e), exc_info=True)
                    report_data['models'][symbol] = {
                        'error': str(e),
                        'status': 'فشل التحليل'
                    }

            self.send_notification('report', report_data)
            return report_data

        except Exception as e:
            error_msg = f"فشل إنشاء تقرير الأداء: {str(e)}"
            self.logger.critical(error_msg, exc_info=True)
            self.send_notification('error', error_msg)
            return {
                'error': error_msg,
                'status': 'فشل حرج'
            }

    def save_state(self):
        state = {
            'current_positions': self.current_positions,
            'last_peaks': self.last_peaks,
            'trailing_stops': self.trailing_stops
        }
        try:
            with open('state.json', 'w') as f:
                json.dump(state, f)
            print("✅ تم حفظ الحالة بنجاح.")
            self.send_notification('update', '💾 تم حفظ الحالة في الملف state.json')
        except Exception as e:
            try:
                # 1. تسجيل الخطأ في نظام اللوجر الرسمي بصيغة lazy formatting
                self.logger.error(
                    "فشل حفظ الحالة - الخطأ: %s",
                    str(e),
                    exc_info=True,
                    stack_info=True,
                    extra={'section': 'state_saving'}
                )

                # 2. إرسال إشعار عاجل مع تفاصيل إضافية
                self.send_notification(
                    'system_error',
                    f"""
                    ⚠️ فشل حرج في حفظ الحالة ⚠️
                    
                    📛 نوع الخطأ: {type(e).__name__}
                    📌 التفاصيل: {str(e)[:200]}
                    📄 الملف: {__file__}
                    ⏰ الوقت: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
                    """
                )

                # 3. محاولة حفظ بدائية للخطأ كملف طوارئ
                try:
                    with open('state_save_failure.txt', 'a', encoding='utf-8') as f:
                        f.write(f"[{datetime.now()}] State Save Failure: {str(e)}\n")
                        traceback.print_exc(file=f)
                except Exception as file_err:
                    self.logger.critical("فشل حفظ ملف الطوارئ: %s", file_err)

            except Exception as logging_error:
                # 4. نظام طوارئ متعدد الطبقات إذا فشل التسجيل
                try:
                    logging.basicConfig(level=logging.CRITICAL)
                    logging.critical("Total failure: %s\nOriginal error: %s", logging_error, e)
                except Exception as fallback_error:
                    sys.stderr.write(f"[ULTIMATE FALLBACK] State save failed: {fallback_error}\n")

    def load_state(self):
        """تحميل الحالة مع التحقق من صحة البيانات وفحص التكامل"""
        try:
            state_file = 'state.json'
            
            # 1. التحقق من وجود الملف
            if not os.path.exists(state_file):
                self.logger.info("⚠️ لم يتم العثور على ملف state.json. سيبدأ البوت بحالة جديدة.")
                self._initialize_default_state()
                return

            # 2. قراءة الملف مع التحقق من صحته
            with open(state_file, 'r') as f:
                try:
                    state = json.load(f)
                except json.JSONDecodeError as e:
                    raise ValueError(f"ملف الحالة تالف ولا يمكن قراءته: {str(e)}")

            # 3. التحقق من الهيكل الأساسي للبيانات
            required_keys = ['current_positions', 'last_peaks', 'trailing_stops']
            for key in required_keys:
                if key not in state:
                    raise ValueError(f"مفتاح مفقود في ملف الحالة: {key}")

            # 4. التحقق من صحة أنواع البيانات
            if not isinstance(state['current_positions'], dict):
                raise TypeError("current_positions يجب أن يكون من نوع dictionary")
            
            if not isinstance(state['last_peaks'], dict):
                raise TypeError("last_peaks يجب أن يكون من نوع dictionary")
                
            if not isinstance(state['trailing_stops'], dict):
                raise TypeError("trailing_stops يجب أن يكون من نوع dictionary")

            # 5. التحقق من التوقيع الرقمي (اختياري)
            if 'checksum' in state:
                self._verify_state_checksum(state)

            # 6. التحقق من توافق الرموز
            for symbol in state['current_positions']:
                if symbol not in self.symbols:
                    self.logger.warning("رمز غير معروف في الحالة المحفوظة: %s", symbol)

            # 7. تعيين القيم مع التحقق من الصحة
            self.current_positions = {
                k: v for k, v in state['current_positions'].items() 
                if self._validate_position_data(v)
            }
            
            self.last_peaks = {
                k: float(v) for k, v in state['last_peaks'].items()
                if k in self.symbols and isinstance(v, (int, float))
            }
            
            self.trailing_stops = {
                k: float(v) for k, v in state['trailing_stops'].items()
                if k in self.symbols and isinstance(v, (int, float))
            }

            self.logger.info("📥 تم تحميل الحالة بنجاح مع التحقق من الصحة")
            self.send_notification('update', '📥 تم تحميل الحالة من state.json بعد التحقق')

        except Exception as e:
            self._handle_state_loading_error(e, state_file)

    def _initialize_default_state(self):
        """تهيئة الحالة الافتراضية"""
        self.current_positions = {}
        self.last_peaks = {}
        self.trailing_stops = {}
        self.logger.info("تم تهيئة الحالة الافتراضية")

    @staticmethod
    def _validate_position_data(position_data):
        """التحقق من صحة بيانات المركز"""
        required_keys = ['entry_price', 'quantity', 'timestamp']
        if not all(k in position_data for k in required_keys):
            return False
            
        try:
            float(position_data['entry_price'])
            float(position_data['quantity'])
            datetime.fromisoformat(position_data['timestamp'])
            return True
        except (ValueError, TypeError):
            return False

    @staticmethod
    def _verify_state_checksum(state):
        """التحقق من checksum البيانات (اختياري)"""
        data_copy = state.copy()
        checksum = data_copy.pop('checksum', None)
        
        if checksum is not None:
            calculated = hashlib.sha256(
                json.dumps(data_copy, sort_keys=True).encode()
            ).hexdigest()
            
            if calculated != checksum:
                raise ValueError("Checksum غير متطابق - البيانات قد تكون معطوبة")

    def _handle_state_loading_error(self, error, state_file):
        """معالجة أخطاء تحميل الحالة"""
        error_msg = f"❌ خطأ في تحميل الحالة: {str(error)}"
        self.logger.error(error_msg, exc_info=True)
        
        # نسخ احتياطي للملف التالف
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        corrupted_file = f"state_corrupted_{timestamp}.json"
        shutil.copyfile(state_file, corrupted_file)
        
        self.logger.info("تم إنشاء نسخة احتياطية من الملف التالف: %s", corrupted_file)
        
        # تهيئة الحالة الافتراضية
        self._initialize_default_state()
        
        self.send_notification(
            'error',
            f"❌ خطأ في تحميل الحالة\n"
            f"📛 {type(error).__name__}\n"
            f"💾 تم الاستعادة للافتراضي\n"
            f"⏰ {datetime.now().strftime('%H:%M')}"
        )

    def handle_binance_error(self, e):
        """معالجة أخطاء Binance المحددة"""
        if isinstance(e, binance.exceptions.BinanceAPIException) and e.code == -1003:
            self.send_notification('warning', "تم تجاوز معدل الطلبات لـ Binance - الانتظار 60 ثانية")
            time.sleep(60)
            return True  # للإشارة لإعادة المحاولة
        return False

    def safe_api_request(self, request_func, service_name, rate_limit=None, max_retries=3):
        """نسخة محسنة مع تتبع المسار الكامل للأخطاء"""
        if rate_limit and rate_limit > 0:
           time.sleep(1.0 / rate_limit)
        for attempt in range(max_retries):
            try:
                response = request_func()

                # تحقق شامل للاستجابة
                if hasattr(response, 'status_code'):
                    if response.status_code == 429:
                        retry_after = int(response.headers.get('Retry-After', 60))
                        self.logger.warning("Rate limited. Retrying after %s s", retry_after)
                        time.sleep(retry_after)
                        continue

                    if response.status_code >= 500:
                        raise APIError(f"Server error: {response.status_code}")

                return response

            except (requests.Timeout, requests.ConnectionError) as e:
                self.logger.error("Network error (attempt %d): %s", attempt + 1, str(e))
                if attempt == max_retries - 1:
                    raise APIConnectionError(f"Failed after {max_retries} attempts")
                time.sleep(2 ** attempt)  # Exponential backoff

            except BinanceAPIException as e:
                self.handle_binance_error(e)
                raise

    @staticmethod
    def _retry_api_request(request_func, *args, max_retries=3, base_delay=1, logger=None, **kwargs):
        """الجزء الخاص بإعادة المحاولة"""
        for attempt in range(max_retries):
            try:
                response = request_func(*args, **kwargs)
                if hasattr(response, 'status_code') and response.status_code != 200:
                    raise Exception(f"كود الخطأ: {response.status_code}")
                return response
            except Exception as e:
                if logger:
                    logger.warning(f"📛 محاولة {attempt+1} فشلت: {str(e)}")
                else:
                    print(f"📛 محاولة {attempt+1} فشلت: {str(e)}")
                if attempt == max_retries - 1:
                    raise
                time.sleep(base_delay * (2 ** attempt))  # Exponential backoff

    def safe_api_call(self, func, *args, **kwargs):
        """
        تنفيذ آمن لطلبات API مع معالجة استثناءات محددة
        """
        try:
            return func(*args, **kwargs)

        except requests.exceptions.Timeout as e:
            self.logger.warning("انتهت مهلة الطلب: %s", str(e))
            raise APITimeoutError(f"مهلة الاتصال: {str(e)}")

        except requests.exceptions.ConnectionError as e:
            self.logger.error("فشل الاتصال: %s", str(e))
            raise APIConnectionError(f"فشل في الاتصال بالخادم: {str(e)}")

        except binance.exceptions.BinanceAPIException as e:
            error_msg = f"خطأ Binance API (كود {e.status_code}): {e.message}"
            self.logger.error(error_msg)
            raise BinanceAPIError(error_msg)

        except json.JSONDecodeError as e:
            self.logger.error("فشل تحليل JSON: %s", str(e))
            raise InvalidResponseError("استجابة API غير صالحة")

        except Exception as e:
            self.logger.critical("خطأ غير متوقع: %s: %s", type(e).__name__, str(e))
            raise APIError(f"فشل غير متوقع في API: {str(e)}")

    def process_trade(self, symbol):
        """
        معالجة الصفقة مع التعامل مع جميع الأخطاء المحتملة بشكل فردي
        """
        try:
            # الحصول على بيانات السوق
            market_data = self.safe_api_call(
                self.client.get_historical_klines,
                symbol, '1h', '1 day ago UTC'
            )

            if not market_data or len(market_data) == 0:
                self.logger.warning("🚫 لا توجد بيانات كافية لـ %s", symbol)
                return None

            # تحليل آخر إغلاق
            latest_close = float(market_data[-1][4])
            self.logger.debug("📊 آخر إغلاق لـ %s: %s", symbol, latest_close)

            # تنفيذ الصفقة
            order = self.safe_api_call(
                self.client.create_order,
                symbol=symbol,
                side='BUY',
                type='MARKET',
                quantity=self.calculate_quantity(symbol)
            )

            return order

        except APITimeoutError:
            self.send_notification('warning', 'مهلة طلب API - إعادة المحاولة...')
            return None

        except BinanceAPIException as e:
            if e.code == -1003:
                self.send_notification('warning', 'تم تجاوز حد الطلبات - الانتظار 60 ثانية')
                time.sleep(60)
                return self.process_trade(symbol)

        except InsufficientFundsError:
            self.send_notification('error', 'رصيد غير كافي للتنفيذ')
            return None

        except Exception as e:
            self.logger.error("فشل غير متوقع في معالجة الصفقة: %s", str(e))
            self.send_notification('error', f'فشل تنفيذ الصفقة: {type(e).__name__}')
            return None

    def execute_trade(self, symbol):
        """تنفيذ الصفقة مع فحص السعر الحالي والتحكم في معدل الطلبات"""
        try:
            # 1. جلب بيانات الشموع (الساعة الماضية)
            data = self.safe_api_request(
                lambda: self.client.get_historical_klines(symbol, '1h', '1 day ago UTC'),
                service_name='binance_klines',
                rate_limit=1
            )

            if not data or len(data) == 0:
                self.logger.warning("❌ لا توجد بيانات شمعات لـ %s", symbol)
                return None

            # 2. استخراج آخر سعر إغلاق (close price)
            latest_close = float(data[-1][4])
            self.logger.debug("🔍 آخر سعر إغلاق لـ %s: %s", symbol, latest_close)

            # (اختياري) مثال: إلغاء الشراء إذا كان السعر مرتفع جدًا
            if latest_close > 10:  # غيّر هذا الشرط حسب استراتيجيتك
                self.logger.info("⛔ السعر مرتفع جدًا لـ %s (%s) — لن يتم تنفيذ الشراء", symbol, latest_close)
                return None

            # 3. تنفيذ أمر الشراء بمعدل 0.5 طلب/ثانية
            order = self.safe_api_request(
                lambda: self.client.create_order(
                    symbol=symbol,
                    side='BUY',
                    type='MARKET',
                    quantity=self.calculate_quantity(symbol)
                ),
                service_name='binance_order',
                rate_limit=0.5
            )
            return order

        except Exception as e:
            self.logger.error("فشل تنفيذ الصفقة لـ %s: %s", symbol, str(e))
            self.send_notification('error',
                f"❌ فشل تنفيذ الصفقة\n"
                f"🪙 {symbol}\n"
                f"📛 {str(e)[:200]}...")
            return None

    def get_historical_data(self, symbol: str, interval: str = '5m', limit: int = None, days: int = None) -> pd.DataFrame:
        """
        نسخة محسنة تدعم كلا الطريقتين (limit و days)
        مع تحسينات للتعامل مع قيود Binance API

        Parameters:
            symbol: رمز التداول (مثل BTCUSDT)
            interval: الإطار الزمني (1m, 5m, 15m, 1h, ...)
            limit: عدد الشموع المطلوبة (اختياري)
            days: عدد الأيام التاريخية (اختياري)
        """
        BINANCE_MAX_LIMIT = 1000  # الحد الأقصى من Binance API

        try:
            # حساب الـ limit إذا تم تحديد الأيام
            if days is not None:
                intervals_per_day = {
                    '1m': 1440,
                    '5m': 288,
                    '15m': 96,
                    '1h': 24,
                    '4h': 6,
                    '1d': 1
                }
                requested_limit = intervals_per_day.get(interval, 288) * days

                if limit is None or requested_limit < limit:
                    limit = requested_limit

            # ضبط الحد الأقصى
            if limit and limit > BINANCE_MAX_LIMIT:
                self.logger.warning("تم تقليل الحد من %s إلى %s بسبب قيود Binance", limit, BINANCE_MAX_LIMIT)
                limit = BINANCE_MAX_LIMIT

            # جلب البيانات
            klines = self.client.get_klines(
                symbol=symbol,
                interval=interval,
                limit=limit or 100  # القيمة الافتراضية
            )

            if not klines:
                raise ValueError("لا توجد بيانات مستلمة")

            df = pd.DataFrame(klines, columns=[
                'timestamp', 'open', 'high', 'low', 'close', 'volume',
                'close_time', 'quote_asset_volume', 'num_trades',
                'taker_buy_base_vol', 'taker_buy_quote_vol', 'ignore'
            ])

            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            df.set_index('timestamp', inplace=True)
            df = df[['open', 'high', 'low', 'close', 'volume']].astype(float)

            if df.empty:
                raise ValueError("البيانات التاريخية فارغة")

            return df

        except Exception as e:
            error_msg = f"فشل جلب البيانات لـ {symbol} على {interval}"
            if limit: error_msg += f" (limit={limit})"
            if days: error_msg += f" (days={days})"
            error_msg += f": {str(e)}"

            self.logger.error(error_msg)
            self.send_notification('error', error_msg[:200])
            return None

    def analyze_multiple_timeframes(self, symbol: str) -> dict:
        """
        تحليل متعدد الأطر الزمنية (5m, 15m, 1h) لعملة محددة

        الميزات:
        - معالجة أخطاء مفصلة لكل إطار زمني
        - تحقق من وجود الأعمدة المطلوبة
        - تسجيل تحذيرات دقيقة
        - كفاءة في استهلاك الموارد

        Returns:
            dict: نتائج التحليل لكل إطار زمني أو {} إذا فشل التحليل
        """
        analysis = {}
        required_indicators = ['ema20', 'ema50', 'rsi', 'macd', 'volume']

        for interval in ['5m', '15m', '1h']:
            try:
                # 1. جلب البيانات
                df = self.get_historical_data(symbol, interval=interval, limit=100)
                if df is None or df.empty:
                    self.logger.warning("بيانات %s على %s فارغة", symbol, interval)
                    continue

                # 2. حساب المؤشرات
                df = self.calculate_technical_indicators(df)

                # 3. التحقق من وجود جميع المؤشرات
                if not all(indicator in df.columns for indicator in required_indicators):
                    missing = [ind for ind in required_indicators if ind not in df.columns]
                    self.logger.warning("مؤشرات مفقودة لـ %s على %s: %s", symbol, interval, missing)
                    continue

                # 4. استخراج القيم
                analysis[interval] = {
                    'ema20': df['ema20'].iloc[-1],
                    'ema50': df['ema50'].iloc[-1],
                    'rsi': df['rsi'].iloc[-1],
                    'macd': df['macd'].iloc[-1],
                    'volume': df['volume'].iloc[-1]
                }

            except Exception as e:
                self.logger.error("فشل تحليل %s لـ %s: %s", interval, symbol, str(e), exc_info=True)
                continue

        return analysis

    @staticmethod
    def _is_connected(timeout=5):
        """الفحص الأساسي لاتصال الإنترنت"""
        try:
            response = requests.get("https://api.binance.com/api/v3/ping", timeout=timeout)
            return response.status_code == 200
        except Exception:
            return False

    def check_internet_connection(self, timeout=5, retries=3):
        """فحص اتصال الإنترنت مع إعادة المحاولة"""
        for i in range(retries):
            if self._is_connected(timeout):
                return True

            if i < retries - 1:  # لا تنام بعد المحاولة الأخيرة
                time.sleep(2 ** i)  # زيادة المهلة تدريجياً
        
        self.send_notification('connection', f'فشل الاتصال بعد {retries} محاولات')
        return False

    def handle_connection_loss(self):
        """إجراءات عند فقدان الاتصال"""
        self.send_notification('error', 'انقطع الاتصال. إعادة المحاولة...')
        time.sleep(60)  # انتظر دقيقة قبل إعادة المحاولة

    @staticmethod
    def initialize_ml_model():
        """
        تهيئة نموذج التعلم الآلي باستخدام XGBoost داخل Pipeline
        
        الميزات:
        - تضمين StandardScaler لتحسين أداء النموذج
        - استخدام XGBClassifier بتعديلات لتقليل overfitting
        - تكوين ثابت وعشوائي لضمان استقرار النتائج
        
        Returns:
            sklearn.pipeline.Pipeline: نموذج مهيأ للتدريب أو التنبؤ
        
        التفاصيل:
        - learning_rate=0.05: تعلم تدريجي أدق
        - max_depth=5: عمق محدود للشجرة لتقليل التعقيد
        - n_estimators=300: عدد أكبر من الأشجار لدقة أفضل
        - subsample=0.8: أخذ عينات جزئية لتقوية التعميم
        - colsample_bytree=0.8: اختيار جزئي للميزات لكل شجرة
        """
        return Pipeline([
            ('scaler', StandardScaler()),
            ('xgb', XGBClassifier(
                objective='binary:logistic',
                learning_rate=0.05,
                max_depth=5,
                n_estimators=300,
                subsample=0.8,
                colsample_bytree=0.8,
                random_state=42,
                eval_metric='logloss'
            ))
        ])

    def retrain_model(self, symbol):        
            self.train_ml_model(symbol)  # سيتم التدريب لكل عملة على حدة
            file_path = f"training_data_{symbol}.csv"
            if not os.path.exists(file_path):
                self.send_notification('warning', f"⚠️ لا يوجد بيانات تدريب لـ {symbol}")
                return

            try:
                df = pd.read_csv(file_path)
                df.dropna(inplace=True)

                required_columns = [
                    'ema20', 'ema50', 'rsi', 'macd',
                    'volume', 'news_sentiment', 'signal_count', 'target'
                ]
                if not all(col in df.columns for col in required_columns):
                    self.send_notification('error', f"❌ الأعمدة ناقصة في {symbol}")
                    return

                X = df[required_columns[:-1]]
                y = df['target']

                X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.2, random_state=42)

                model = self.initialize_ml_model()
                model.fit(X_train, y_train)

                y_pred = model.predict(X_test)
                acc = accuracy_score(y_test, y_pred)
                prec = precision_score(y_test, y_pred, zero_division=0)
                rec = recall_score(y_test, y_pred, zero_division=0)

                self.send_notification('report', f"📊 {symbol} — دقة: {acc:.4f}, الدقة: {prec:.4f}, الاسترجاع: {rec:.4f}")

                model_path = f"xgb_model_{symbol}.pkl"
                joblib.dump(model, open(model_path, 'wb'))
                self.models[symbol] = model

            except Exception as e:
                self.send_notification('error', f"❌ فشل تدريب النموذج لـ {symbol}: {e}")

    def start_bot(self):
        """يبدأ تشغيل البوت مع إشعار"""
        self.is_running = True
        self.start_time = datetime.now()
        self.send_notification('start')
        print("تم تشغيل البوت")

    def shutdown_bot(self, reason="إيقاف طبيعي"):
        """يوقف البوت مع إشعار"""
        self.is_running = False
        self.send_notification('shutdown', {'reason': reason})
        print(f"تم إيقاف البوت. السبب: {reason}")

    # نظام المؤشرات الفنية المتكامل
    def calculate_technical_indicators(self, df):
        """
        حساب المؤشرات الفنية مع ضمانات كاملة ضد الأخطاء
        """
        try:
            # ===== 1. التحقق من صحة البيانات المدخلة =====
            required_columns = {
                'open': 'سعر الافتتاح',
                'high': 'أعلى سعر',
                'low': 'أقل سعر',
                'close': 'سعر الإغلاق',
                'volume': 'حجم التداول'
            }

            missing_columns = [name for col, name in required_columns.items()
                               if col not in df.columns]
            if missing_columns:
                error_msg = f"أعمدة مفقودة: {', '.join(missing_columns)}"
                self.logger.error(error_msg)
                raise ValueError(error_msg)

            if df[list(required_columns.keys())].isnull().any().any():
                error_msg = "توجد قيم فارغة في البيانات الأساسية"
                self.logger.error(error_msg)
                raise ValueError(error_msg)

            # ===== 2. حساب المؤشرات الفنية =====
            indicators = {}

            indicators['ema20'] = self._safe_calculate_indicator(
                lambda: EMAIndicator(close=df['close'], window=20).ema_indicator(),
                'EMA 20'
            )

            indicators['ema50'] = self._safe_calculate_indicator(
                lambda: EMAIndicator(close=df['close'], window=50).ema_indicator(),
                'EMA 50'
            )

            indicators['rsi'] = self._safe_calculate_indicator(
                lambda: RSIIndicator(close=df['close'], window=14).rsi(),
                'RSI'
            )

            macd_line = self._safe_calculate_indicator(
                lambda: MACD(close=df['close']).macd(),
                'MACD Line'
            )
            signal_line = self._safe_calculate_indicator(
                lambda: MACD(close=df['close']).macd_signal(),
                'MACD Signal'
            )

            if macd_line is not None and signal_line is not None:
                indicators['macd'] = macd_line
                indicators['macd_signal'] = signal_line

            indicators['bb_upper'] = self._safe_calculate_indicator(
                lambda: BollingerBands(close=df['close']).bollinger_hband(),
                'Bollinger Upper'
            )

            indicators['bb_lower'] = self._safe_calculate_indicator(
                lambda: BollingerBands(close=df['close']).bollinger_lband(),
                'Bollinger Lower'
            )

            indicators['adx'] = self._safe_calculate_indicator(
                lambda: ADXIndicator(
                    high=df['high'],
                    low=df['low'],
                    close=df['close'],
                    window=14
                ).adx(),
                'ADX'
            )

            # ===== 3. دمج النتائج =====
            for name, values in indicators.items():
                if values is not None:
                    df[name] = values

            # ===== 4. التحقق النهائي =====
            required_indicators = ['ema20', 'ema50', 'rsi']
            for indicator in required_indicators:
                if indicator not in df.columns or df[indicator].isnull().all():
                    error_msg = f"فشل حساب المؤشر الأساسي: {indicator}"
                    self.logger.error(error_msg)
                    raise RuntimeError(error_msg)

            self.logger.info("تم حساب المؤشرات الفنية بنجاح")
            return df

        except ValueError as ve:
            self.send_notification(
                'error',
                f"📊 خطأ في بيانات المؤشرات\n📌 {str(ve)}\n⏰ {datetime.now().strftime('%H:%M')}"
            )
            raise

        except Exception as e:
            error_msg = f"فشل غير متوقع في حساب المؤشرات: {type(e).__name__}: {str(e)}"
            self.logger.critical(error_msg, exc_info=True)
            self.send_notification(
                'error',
                f"📊 انهيار حساب المؤشرات\n📛 {type(e).__name__}\n⏰ {datetime.now().strftime('%H:%M')}"
            )
            raise

    def _safe_calculate_indicator(self, indicator_func, indicator_name):
        """
        دالة مساعدة لحساب المؤشرات بشكل آمن مع معالجة شاملة للأخطاء

        الميزات:
        - تحقق من صحة المؤشر المحسوب
        - تسجيل مفصل للأخطاء
        - عدم توقف البرنامج عند فشل مؤشر واحد
        - توثيق كامل للدالة

        Args:
            indicator_func: دالة حساب المؤشر (lambda function)
            indicator_name: اسم وصفي للمؤشر

        Returns:
            pandas.Series: سلسلة تحتوي على قيم المؤشر
            None: إذا فشل الحساب

        Examples:
            >>> _safe_calculate_indicator(lambda: EMAIndicator(close=df['close']).ema_indicator(), "EMA 20")
        """
        try:
            # 1. حساب المؤشر
            result = indicator_func()

            # 2. التحقق من أن النتيجة ليست فارغة
            if result is None:
                raise ValueError("دالة المؤشر أعادت قيمة None")

            # 3. التحقق من نوع ونوعية البيانات
            if not isinstance(result, pd.Series):
                raise TypeError(f"الناتج يجب أن يكون pandas.Series وليس {type(result)}")

            # 4. التحقق من عدم وجود قيم فارغة
            if result.isnull().any():
                nan_count = result.isnull().sum()
                raise ValueError(f"يوجد {nan_count} قيم فارغة في الناتج")

            # 5. التحقق من طول السلسلة
            if len(result) == 0:
                raise ValueError("السلسلة الناتجة فارغة")

            return result

        except ValueError as ve:
            error_msg = f"خطأ في قيمة مؤشر {indicator_name}: {str(ve)}"
            self.logger.warning(error_msg)
            return None

        except TypeError as te:
            error_msg = f"خطأ في نوع مؤشر {indicator_name}: {str(te)}"
            self.logger.warning(error_msg)
            return None

        except Exception as e:
            error_msg = f"فشل غير متوقع في حساب مؤشر {indicator_name}: {type(e).__name__}: {str(e)}"
            self.logger.error(error_msg, exc_info=True)
            return None

    def check_timeframe_divergence(self, symbol):
        """
        التحقق من وجود تباعد بين الأطر الزمنية المختلفة
        """
        analysis = self.analyze_multiple_timeframes(symbol)
        
        if not all(k in analysis for k in ['5m', '15m', '1h']):
            return False

        # استخراج القيم لتقليل التكرار
        rsi_5m = analysis['5m']['rsi']
        rsi_15m = analysis['15m']['rsi']
        macd_5m = analysis['5m']['macd']
        macd_15m = analysis['15m']['macd']

        # تباعد RSI
        rsi_divergence = (rsi_5m > 70 > rsi_15m) or (rsi_5m < 30 < rsi_15m)

        # تباعد MACD
        macd_divergence = (macd_5m > 0 > macd_15m) or (macd_5m < 0 < macd_15m)

        return rsi_divergence or macd_divergence

    def backtest_strategy(self, symbol: str, days: int = 90, interval: str = '5m') -> dict:
        """
        اختبار تاريخي لاستراتيجية التداول على بيانات سابقة
        """
        try:
            # جلب البيانات التاريخية
            df = self.get_historical_data(symbol, interval=interval, limit=days*288)  # 288 = عدد الشموع في اليوم لـ5m

            if df is None or len(df) < 100:
                return {'error': 'لا توجد بيانات كافية للاختبار'}

            # حساب المؤشرات الفنية
            df = self.calculate_technical_indicators(df)

            # محاكاة الصفقات
            trades = []
            in_position = False
            entry_price = 0
            entry_time = None

            for i in range(1, len(df)):
                current = df.iloc[i]
                previous = df.iloc[i-1]

                # شروط الدخول مع استخدام previous
                entry_conditions = (
                    current['ema20'] > current['ema50'] and
                    previous['ema20'] <= previous['ema50'] and
                    current['rsi'] > 50 and
                    current['macd'] > current['macd_signal'] and
                    not in_position
                )

                # شروط الخروج كما هي بدون تعديل
                exit_conditions = (
                    in_position and 
                    (current['close'] < current['ema20'] or
                     current['rsi'] > 70 or
                     current['close'] <= entry_price * 0.95)
                )

                # تنفيذ الدخول
                if entry_conditions:
                    in_position = True
                    entry_price = current['close']
                    entry_time = current.name

                # تنفيذ الخروج
                elif exit_conditions and in_position:
                    exit_price = current['close']
                    profit_pct = (exit_price - entry_price) / entry_price * 100
                    duration = (current.name - entry_time).total_seconds() / 60  # المدة بالدقائق

                    trades.append({
                        'entry_price': entry_price,
                        'exit_price': exit_price,
                        'profit_pct': profit_pct,
                        'duration': duration,
                        'entry_time': entry_time,
                        'exit_time': current.name
                    })

                    in_position = False

            # حساب مقاييس الأداء
            if not trades:
                return {'error': 'لم يتم تنفيذ أي صفقات خلال الفترة'}

            winning_trades = [t for t in trades if t['profit_pct'] > 0]
            losing_trades = [t for t in trades if t['profit_pct'] <= 0]

            results = {
                'total_trades': len(trades),
                'win_rate': len(winning_trades) / len(trades),
                'avg_profit': sum(t['profit_pct'] for t in trades) / len(trades),
                'max_profit': max(t['profit_pct'] for t in trades),
                'max_loss': min(t['profit_pct'] for t in trades),
                'profit_factor': (sum(t['profit_pct'] for t in winning_trades) / 
                                  abs(sum(t['profit_pct'] for t in losing_trades))) if losing_trades else float('inf'),
                'avg_duration': sum(t['duration'] for t in trades) / len(trades),
                'trades': trades[:50]  # حفظ أول 50 صفقة فقط للتحليل
            }

            return results

        except Exception as e:
            self.logger.error("فشل في الاختبار التاريخي لـ %s: %s", symbol, str(e), exc_info=True)
            return {'error': str(e)}

    def optimize_entry_conditions(self, symbol: str, test_periods: list = None) -> dict:
        """
        تحسين معايير الدخول باستخدام البحث الشبكي مع تقييم متعدد المقاييس

        التحسينات الرئيسية:
        - تحليل عدة فترات زمنية
        - اختيار المعلمات المثلى بناءً على الأداء
        """
        if test_periods is None:
            test_periods = [30, 60, 90]
        try:
            # 1. تحميل بيانات التدريب
            data = self._load_training_data(symbol)
            if data is None:
                return {'error': 'لا توجد بيانات تدريب كافية'}

            # 2. تقسيم البيانات مع الحفاظ على التسلسل الزمني
            X = data.drop('target', axis=1)
            y = data['target']

            # 3. تعريف مساحة البحث
            param_grid = {
                'rsi_min': [40, 45, 50, 55],
                'ema_cross': [True, False],
                'macd_condition': [True, False],
                'news_threshold': [0.1, 0.2, 0.3],
                'min_signals': [1, 2, 3],
                'timeframe_confirmations': [1, 2]
            }

            # 4. دالة تقييم مخصصة تأخذ في الاعتبار الربحية
            def profit_scorer(estimator, X, _):
                y_pred = estimator.predict(X)
                profit = (y_pred * X['expected_profit']).sum()
                return profit

            # 5. إعداد البحث الشبكي
            grid = GridSearchCV(
                estimator=XGBClassifier(),
                param_grid=param_grid,
                scoring=profit_scorer,
                cv=TimeSeriesSplit(n_splits=3),
                n_jobs=-1,
                verbose=1
            )

            # 6. تنفيذ البحث
            grid.fit(X, y)

            # 7. تحليل نتائج الوقت الأمثل
            time_analysis = self._analyze_optimal_times(data)

            # 8. حفظ النتائج
            best_params = {
                **grid.best_params_,
                'best_score': grid.best_score_,
                'time_analysis': time_analysis
            }

            self._save_optimization_results(symbol, best_params)

            return best_params

        except Exception as e:
            self.logger.error("فشل تحسين المعايير لـ %s: %s", symbol, str(e), exc_info=True)
            return {'error': str(e)}

    def _analyze_optimal_times(self, data: pd.DataFrame) -> dict:
        """
        تحليل متقدم لأوقات السوق المثلى للتداول

        الميزات:
        1. تحليل الأداء حسب ساعات اليوم
        2. تحليل الأداء حسب أيام الأسبوع
        3. تحديد فترات التقلب العالي
        4. تحليل تأثير العطلات والأحداث العالمية

        Returns:
            dict: نتائج التحليل الزمني
        """
        try:
            if 'timestamp' not in data.columns:
                data['timestamp'] = data.index

            # 1. تحليل حسب ساعات اليوم
            data['hour'] = data['timestamp'].dt.hour
            hourly = data.groupby('hour').agg({
                'target': ['mean', 'count'],
                'rsi': 'mean',
                'volume': 'mean'
            })

            # 2. تحليل حسب أيام الأسبوع
            data['weekday'] = data['timestamp'].dt.weekday
            weekday = data.groupby('weekday').agg({
                'target': ['mean', 'count'],
                'rsi': 'mean',
                'volume': 'mean'
            })

            # 3. تحديد فترات التقلب العالي
            data['volatility'] = data['high'] - data['low']
            volatile_hours = data.groupby('hour')['volatility'].mean().nlargest(3).index.tolist()

            # 4. تحليل العطلات
            holiday_analysis = self._analyze_holiday_performance(data)

            return {
                'best_hours': hourly['target']['mean'].nlargest(3).index.tolist(),
                'worst_hours': hourly['target']['mean'].nsmallest(3).index.tolist(),
                'best_weekdays': weekday['target']['mean'].nlargest(3).index.tolist(),
                'volatile_hours': volatile_hours,
                'holiday_effect': holiday_analysis,
                'hourly_stats': hourly.to_dict(),
                'weekday_stats': weekday.to_dict()
            }

        except Exception as e:
            self.logger.error("فشل تحليل أوقات السوق: %s", str(e), exc_info=True)
            return {'error': str(e)}

    def _analyze_holiday_performance(self, data: pd.DataFrame) -> dict:
        """
        تحليل أداء التداول خلال العطلات والأحداث العالمية

        الميزات:
        1. دعم متعدد البلدان
        2. تحليل قبل وبعد الأحداث الهامة
        3. تكامل مع تقويمات الأحداث الاقتصادية
        """
        try:
            # 1. تحديد العطلات الرئيسية
            us_holidays = holidays.US()
            uk_holidays = holidays.UK()

            # 2. تصنيف الأيام
            data['is_holiday'] = data['timestamp'].apply(
                lambda x: x in us_holidays or x in uk_holidays
            )

            # 3. تحليل الأداء
            holiday_stats = data.groupby('is_holiday')['target'].agg(['mean', 'count'])

            # 4. تحليل الأحداث الاقتصادية (يمكن إضافة مصدر بيانات هنا)
            event_dates = self._get_economic_events(data['timestamp'].min(), data['timestamp'].max())
            data['is_event_day'] = data['timestamp'].isin(event_dates)
            event_stats = data.groupby('is_event_day')['target'].agg(['mean', 'count'])

            return {
                'holiday_performance': holiday_stats.to_dict(),
                'event_performance': event_stats.to_dict(),
                'recommendation': "تجنب التداول خلال العطلات" if holiday_stats.loc[True, 'mean'] < 0.5 else "لا يوجد تأثير سلبي للعطلات"
            }

        except Exception as e:
            self.logger.error("فشل تحليل العطلات: %s", str(e), exc_info=True)
            return {'error': str(e)}

    def auto_optimize_strategy(self, symbol: str):
        """
        نظام التحسين التلقائي الشامل الذي يجمع بين:
        1. تحليل المعايير
        2. تحليل أوقات السوق
        3. التعلم الآلي التكيفي

        الميزات:
        - تحديث النموذج تلقائياً ببيانات جديدة
        - ضبط المعايير ديناميكياً
        - التكيف مع ظروف السوق المتغيرة
        """
        try:
            # 1. جمع البيانات الحديثة
            self.update_training_data(symbol)

            # 2. تحسين المعايير
            optimization_results = self.optimize_entry_conditions(symbol)

            # 3. تدريب النموذج مع المعايير الجديدة
            model = self.train_ml_model(symbol)

            # 4. تحليل أداء النموذج
            performance = self.evaluate_model_performance(model, symbol)

            # 5. تطبيق التغييرات إذا كانت النتائج جيدة
            if performance.get('profit_factor', 0) > 1.5:
                self.apply_new_parameters(symbol, optimization_results)
                return {
                    'status': 'success',
                    'optimized_params': optimization_results,
                    'model_performance': performance
                }
            else:
                return {
                    'status': 'no_improvement',
                    'message': 'لم يتم تحقيق تحسن كافي'
                }

        except Exception as e:
            self.logger.error("فشل التحسين التلقائي: %s", str(e), exc_info=True)
            return {'status': 'error', 'message': str(e)}

    def save_optimization_results(self, symbol: str, results: dict):
        """
        حفظ نتائج تحسين المعايير في ملف JSON
        """
        try:
            os.makedirs('optimization_results', exist_ok=True)
            file_path = f'optimization_results/{symbol}_{datetime.now().strftime("%Y%m%d")}.json'
            
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump({
                    'symbol': symbol,
                    'timestamp': datetime.now().isoformat(),
                    'results': results
                }, f, indent=2, ensure_ascii=False)
                
            self.logger.info("تم حفظ نتائج تحسين %s في %s", symbol, file_path)
            
        except Exception as e:
            self.logger.error("فشل في حفظ نتائج التحسين: %s", str(e), exc_info=True)

    def _process_coin_with_strategy(self, symbol: str, aggressive: bool = False):
        """معالجة العملة باستخدام الإستراتيجية المحددة"""
        if aggressive:
            self._process_coin_aggressive(symbol)
        else:
            self._process_coin_conservative(symbol)

    def analyze_market_timing(self):
        """تحليل توقيت السوق الأمثل وحفظ النتائج"""
        analysis = {}
        for symbol in self.symbols:
            data = self.get_historical_data(symbol, '1h', days=30)
            if data is not None:
                analysis[symbol] = self._analyze_optimal_times(data)
        
        # تحديد الساعات المثلى بناء على جميع الرموز
        all_hours = []
        for symbol_analysis in analysis.values():
            all_hours.extend(symbol_analysis.get('best_hours', []))
        
        self.optimal_trading_hours = list(set(all_hours))  # إزالة التكرارات
        
        self.save_market_timing_analysis(analysis)
        
    @staticmethod
    def _validate_indicators(df):
        """التحقق من صحة المؤشرات المحسوبة"""
        required_indicators = ['ema20', 'ema50', 'rsi']
        for indicator in required_indicators:
            if indicator not in df.columns:
                raise ValueError(f"المؤشر {indicator} غير موجود في النتائج")
            if df[indicator].isnull().any():
                raise ValueError(f"توجد قيم مفقودة في مؤشر {indicator}")

    def get_account_balance(self):
        def fetch_balance():
            return self.client.get_account()
        
        try:
            return self.safe_api_request(
                fetch_balance,
                service_name='binance',
                rate_limit=0.5  # طلبين في الثانية كحد أقصى
            )
        except Exception as e:
                 self.send_notification('error', f"فشل جلب الرصيد: {str(e)}")
                 return None

    @staticmethod
    def generate_recommendations(results: dict) -> list:
        """
        توليد توصيات تلقائية بناءً على نتائج الاختبار
        
        الميزات:
        - تحليل لمقاييس الأداء الأساسية
        - اقتراحات ذكية لتحسين الاستراتيجية
        - دعم لمزيد من التوصيات المستقبلية
        """
        recs = []

        if results.get('win_rate', 0) < 0.6:
            recs.append("زيادة متطلبات الدخول (مثل رفع حد RSI الأدنى)")

        if results.get('avg_duration', 0) > 180:
            recs.append("تشديد شروط الخروج لتقليل مدة الاحتفاظ بالصفقات")

        if results.get('max_loss', 0) < -8:
            recs.append("إضافة أو تعديل وقف الخسارة المتحرك")

        return recs if recs else ["لا توجد توصيات - الأداء جيد"]

    def get_optimization_report(self, symbol: str) -> str:
        """
        إنشاء تقرير عن نتائج التحسين
        
        الميزات:
        - دمج نتائج backtesting مع التحليل والتوصيات
        - توليد تقرير منسق بلغة واضحة
        - معالجة شاملة للأخطاء
        """
        try:
            params = self.load_optimized_params(symbol)
            if not params:
                return f"⚠️ لا توجد نتائج تحسين لـ {symbol}"
                
            backtest = self.backtest_strategy(symbol)
            analysis = self.analyze_backtest_results(backtest)
            
            report = (
                f"📊 تقرير تحسين {symbol}\n"
                f"📅 آخر تحديث: {params.get('last_updated', 'غير معروف')}\n"
                f"📈 نسبة النجاح: {analysis['overall'].get('win_rate', 0) * 100:.1f}%\n"
                f"💰 متوسط الربح: {analysis['overall'].get('avg_profit', 0):.2f}%\n"
                f"🔍 عدد الصفقات: {analysis['overall'].get('total_trades', 0)}\n"
                f"🕒 أفضل وقت للتداول: {max(analysis['hourly_analysis'].items(), key=lambda x: x[1]['avg_profit'])[0]}:00\n"
                f"📌 التوصيات:\n- " + "\n- ".join(analysis.get('recommendations', ['لا توجد توصيات']))
            )
            
            return report
            
        except Exception as e:
            return f"❌ فشل في إنشاء التقرير: {str(e)}"

    def analyze_backtest_results(self, results: dict) -> dict:
        """
        تحليل متقدم لنتائج الاختبار التاريخي
        """
        if 'error' in results:
            return results

        try:
            trades = results['trades']

            # تحليل حسب الوقت من اليوم
            hour_groups = {h: [] for h in range(24)}
            for trade in trades:
                hour = trade['entry_time'].hour
                hour_groups[hour].append(trade['profit_pct'])

            hour_analysis = {
                h: {
                    'avg_profit': sum(profts)/len(profts) if profts else 0,
                    'win_rate': len([p for p in profts if p > 0])/len(profts) if profts else 0,
                    'trade_count': len(profts)
                }
                for h, profts in hour_groups.items()
            }

            # تحليل حسب يوم الأسبوع
            weekday_groups = {d: [] for d in range(7)}
            for trade in trades:
                weekday = trade['entry_time'].weekday()
                weekday_groups[weekday].append(trade['profit_pct'])

            weekday_analysis = {
                d: {
                    'avg_profit': sum(profts)/len(profts) if profts else 0,
                    'win_rate': len([p for p in profts if p > 0])/len(profts) if profts else 0,
                    'trade_count': len(profts)
                }
                for d, profts in weekday_groups.items()
            }

            return {
                'overall': results,
                'hourly_analysis': hour_analysis,
                'weekday_analysis': weekday_analysis,
                'recommendations': self.generate_recommendations(results)
            }

        except Exception as e:
            return {'error': f'فشل في تحليل النتائج: {str(e)}'}

    def execute_buy_order(self, symbol):
        """
        تنفيذ أمر شراء مع ضمانات كاملة ضد الأخطاء
        """
        try:
            # 1. الحصول على الرصيد المتاح
            balance = float(self.client.get_asset_balance('USDT')['free'])
            if balance <= 6:  # حد أدنى 10 USDT
                self.send_notification('warning', f'رصيد غير كافي لـ {symbol}: {balance:.2f} USDT')
                return None

            # 2. الحصول على سعر السوق
            ticker = self.client.get_symbol_ticker(symbol=symbol)
            current_price = float(ticker['price'])
            if current_price <= 0:
                raise ValueError(f"سعر غير صالح: {current_price}")

            # 3. حساب الكمية
            step_size, min_qty = self.get_trade_limits(symbol)
            quantity = (balance * 0.3) / current_price  # استثمار 20% من الرصيد
            quantity = float(np.floor(quantity / step_size) * step_size)  # التقريب للأسفل

            # 4. التحقق الحاسم من الكمية
            if quantity <= min_qty:
                error_msg = f'كمية غير صالحة لـ {symbol}: {quantity:.6f} (الحد الأدنى: {min_qty:.6f})'
                self.logger.error(error_msg)
                self.send_notification('error', error_msg)
                return None

            # 5. تنفيذ الأمر
            order = self.client.create_order(
                symbol=symbol,
                side=Client.SIDE_BUY,
                type=Client.ORDER_TYPE_MARKET,
                quantity=quantity
            )

            # 6. تحديث المراكز المفتوحة
            self.current_positions[symbol] = {
                'entry_price': current_price,
                'quantity': quantity,
                'timestamp': datetime.now(),
            }

            # 7. إرسال إشعار الشراء
            self.send_notification(
                'buy',
                f"✅ تم الشراء\n"
                f"🪙 {symbol}\n"
                f"💰 السعر: {current_price:.4f}\n"
                f"📊 الكمية: {quantity:.4f}\n"
                f"💵 القيمة: {(quantity*current_price):.2f} USDT"
            )

            return order

        except binance.exceptions.BinanceAPIException as api_error:
            error_msg = f"خطأ Binance في الشراء: {api_error.code} - {api_error.message}"
            self.logger.error(error_msg)
            self.send_notification('error', f'❌ فشل شراء {symbol[:4]}...')
            return None

        except Exception as e:
            error_msg = f"فشل غير متوقع في الشراء: {type(e).__name__}: {str(e)}"
            self.logger.error(error_msg, exc_info=True)
            self.send_notification('error', f'❌ خطأ عام في {symbol[:4]}...')
            return None

    def _process_coin(self, symbol):
        """
        معالجة متقدمة لكل عملة مع نظام متكامل لإدارة الأخطاء وتحليل متعدد الأطر الزمنية
        """
        self.logger.info("بدأ معالجة %s", symbol)
        start_time = time.time()
        processed_successfully = False

        try:
            # ===== 1. تحديث بيانات الأخبار =====
            try:
                self.update_news_sentiment(symbol)
                self.logger.debug("تم تحديث أخبار %s", symbol)
            except Exception as news_error:
                self.logger.error("أخبار %s | %s: %s", symbol, type(news_error).__name__, str(news_error), exc_info=True)
                self.send_notification('warning', f"⚠️ أخبار {symbol[:4]}...")

            # ===== 2. تحديث الإشارات الاحترافية =====
            try:
                signal_count_before = len(self.pro_signals.get(symbol, []))
                self.update_pro_signals(symbol)
                signal_count_after = len(self.pro_signals.get(symbol, []))
                self.logger.debug("إشارات %s: %d جديدة", symbol, signal_count_after - signal_count_before)
            except Exception as signal_error:
                self.logger.error("إشارات %s | %s: %s", symbol, type(signal_error).__name__, str(signal_error), exc_info=True)

            # ===== 3. جلب البيانات الأساسية (5m) =====
            try:
                df_5m = self.get_historical_data(symbol, interval='5m', limit=100)
                if df_5m is None or df_5m.empty:
                    self.logger.error("بيانات %s (5m) فارغة", symbol)
                    self.send_notification('warning', f"📉 بيانات {symbol[:4]} (5m)...")
                    return
            except Exception as data_error:
                self.logger.critical("بيانات %s | %s: %s", symbol, type(data_error).__name__, str(data_error), exc_info=True)
                self.send_notification('error', f"❌ بيانات {symbol[:4]}...")
                return

            # ===== 4. التحليل الفني (5m) =====
            try:
                df_5m = self.calculate_technical_indicators(df_5m)
                required_indicators = ['ema20', 'ema50', 'rsi', 'macd']
                if not all(col in df_5m.columns for col in required_indicators):
                    missing = [col for col in required_indicators if col not in df_5m.columns]
                    raise ValueError(f"مؤشرات فنية ناقصة: {missing}")

                self.logger.debug(
                    "تحليل %s (5m): EMA20=%.4f, RSI=%.2f",
                    symbol,
                    df_5m['ema20'].iloc[-1],
                    df_5m['rsi'].iloc[-1]
                )
            except Exception as ta_error:
                self.logger.error("تحليل فني %s | %s: %s", symbol, type(ta_error).__name__, str(ta_error), exc_info=True)
                self.send_notification('error', f"📊 تحليل {symbol[:4]}...")
                return

            # ===== 5. تحليل الأطر الزمنية الأخرى =====
            timeframe_analysis = {}
            try:
                timeframe_analysis = self.analyze_multiple_timeframes(symbol)
                if not timeframe_analysis:
                    self.logger.warning("تحليل الأطر الزمنية لـ %s لم يعط نتائج", symbol)
            except Exception as timeframe_error:
                self.logger.error("أطر زمنية %s | %s: %s", symbol, type(timeframe_error).__name__, str(timeframe_error), exc_info=True)

            # ===== 6. تقييم شروط الدخول =====
            try:
                if self.evaluate_entry_conditions(df_5m, symbol):
                    self.logger.info("إشارة شراء لـ %s بناءً على تحليل متعدد الأطر", symbol)

                    # ===== 7. تنفيذ أمر الشراء =====
                    try:
                        order_result = self.execute_buy_order(symbol)
                        if order_result:
                            self.logger.info("تم تنفيذ أمر شراء %s", symbol)
                            processed_successfully = True
                        else:
                            self.logger.warning("فشل تنفيذ شراء %s", symbol)
                    except Exception as order_error:
                        self.logger.error("تنفيذ أمر %s | %s: %s", symbol, type(order_error).__name__, str(order_error), exc_info=True)
                        self.send_notification('error', f"💸 تنفيذ {symbol[:4]}...")
            except Exception as evaluation_error:
                self.logger.error("تقييم %s | %s: %s", symbol, type(evaluation_error).__name__, str(evaluation_error), exc_info=True)

        except Exception as global_error:
            self.logger.critical("فشل عام في %s | %s: %s", symbol, type(global_error).__name__, str(global_error), exc_info=True)
            self.send_notification(
                'error',
                f"⛔ فشل في {symbol[:4]}\n"
                f"📛 {type(global_error).__name__}\n"
                f"⏳ {datetime.now().strftime('%H:%M')}"
            )
        finally:
            exec_time = time.time() - start_time
            status = "بنجاح" if processed_successfully else "بفشل"
            self.logger.info("انتهت معالجة %s %s في %.2f ثانية", symbol, status, exec_time)

    def manage_all_positions(self):
        """
        النسخة المعدلة التي تبيع فقط عند:
        1. تحقيق الربح الأدنى (min_profit) 
        2. لمس سعر التريلينغ ستوب
        معًا!
        """
        if not self.current_positions:
            return

        for symbol, position in list(self.current_positions.items()):
            if not position:
                continue

            try:
                # 1. الحصول على البيانات الأساسية
                ticker = self.client.get_symbol_ticker(symbol=symbol)
                current_price = float(ticker['price'])
                entry_price = position['entry_price']
                profit_percent = (current_price - entry_price) / entry_price * 100

                # 2. تحديث التريلينغ ستوب فقط إذا حققنا الربح الأدنى
                if profit_percent >= self.min_profit:
                    new_stop = current_price * (1 - self.trailing_percent / 100)
                    if symbol not in self.trailing_stops or new_stop > self.trailing_stops[symbol]:
                        self.trailing_stops[symbol] = new_stop
                        self.logger.debug("Updated trailing for %s: %.4f", symbol, new_stop)

                # 3. البيع فقط إذا تحقق الشرطان معًا
                if (profit_percent >= self.min_profit and 
                    symbol in self.trailing_stops and 
                    current_price < self.trailing_stops[symbol]):
                    
                    duration = datetime.now() - position['timestamp']
                    self._execute_sell_order(
                        symbol=symbol,
                        price=current_price,
                        position=position,
                        profit=profit_percent,
                        duration=duration,
                        reason="Both conditions met"
                    )

            except binance.exceptions.BinanceAPIException as e:
                error_msg = f"Binance error for {symbol}: {e.status_code}"
                self.logger.error(error_msg)
                self.send_notification('error', error_msg[:200])

            except Exception as e:
                error_msg = f"Error managing {symbol}: {str(e)}"
                self.logger.error(error_msg, exc_info=True)
                self.send_notification('error', error_msg[:200])

    def _execute_sell_order(self, symbol, price, position, profit, duration, reason=None):
        """
        تنفيذ أمر بيع آمن مع تنظيف كامل للبيانات

        Parameters:
            symbol (str): رمز العملة (مثل BTCUSDT)
            price (float): سعر البيع الحالي
            position (dict): تفاصيل المركز المفتوح
            profit (float): نسبة الربح/الخسارة
            duration (timedelta): مدة الاحتفاظ بالصفقة

        Returns:
            dict: نتيجة الأمر من البورصة

        Raises:
            Exception: إذا فشل تنفيذ الأمر
        """
        try:
            # 1. تنفيذ أمر البيع
            order = self.client.create_order(
                symbol=symbol,
                side=Client.SIDE_SELL,
                type=Client.ORDER_TYPE_MARKET,
                quantity=position['quantity']
            )

            # 2. إرسال إشعار البيع
            self.send_notification('sell', {
                'symbol': symbol,
                'quantity': position['quantity'],
                'price': price,
                'profit': f"{profit:.2f}%",
                'duration': str(duration),
                'entry_price': position['entry_price']
            })

            # 3. تنظيف كافة البيانات المرتبطة
            with self.lock:  # استخدام القفل لمنع التنافسية
                # أ. إزالة المركز المفتوح
                if symbol in self.current_positions:
                    del self.current_positions[symbol]

                # ب. إزالة وقف الخسارة المتابع
                self.trailing_stops.pop(symbol, None)

                # ج. إزالة القمم السابقة (المضافة منك)
                if symbol in self.last_peaks:
                    del self.last_peaks[symbol]

                # د. إزالة مستويات فيبوناتشي إن وجدت
                if symbol in self.fib_levels:
                    del self.fib_levels[symbol]

                # هـ. إزالة نقاط البيفوت إن وجدت
                if symbol in self.pivot_points:
                    del self.pivot_points[symbol]

            return order

        except Exception as e:
            error_msg = f"فشل تنفيذ البيع لـ {symbol}: {str(e)}"
            self.logger.error(error_msg, exc_info=True)
            self.send_notification('error', error_msg)
            raise
            
    def _calculate_fibonacci_levels(self, df):
        """حساب مستويات فيبوناتشي مع التحقق من الصحة"""
        try:
            high = df['high'].max()
            low = df['low'].min()

            if pd.isna(high) or pd.isna(low):
                raise ValueError("قيم high/low غير صالحة")

            diff = high - low
            if diff <= 0:
                raise ValueError("فرق غير صالح بين high و low")

            self.fib_levels = {
                '38.2%': high - diff * 0.382,
                '50%': high - diff * 0.5,
                '61.8%': high - diff * 0.618
            }

        except Exception as e:
            self.logger.error("فشل حساب مستويات فيبوناتشي: %s", str(e))
            self.fib_levels = {}

    def _calculate_pivot_points(self, df):
        """حساب نقاط البيفوت مع التحقق من الصحة"""
        try:
            if len(df) < 1:
                raise ValueError("لا توجد بيانات كافية لحساب البيفوت")

            day_df = df.resample('1D').agg({
                'high': 'max',
                'low': 'min',
                'close': 'last'
            }).dropna()

            if len(day_df) < 1:
                raise ValueError("لا توجد بيانات يومية كافية")

            pivot = (day_df['high'] + day_df['low'] + day_df['close']) / 3
            self.pivot_points = {
                'pivot': pivot.iloc[-1],
                'R1': (2 * pivot - day_df['low']).iloc[-1],
                'S1': (2 * pivot - day_df['high']).iloc[-1]
            }

        except Exception as e:
            self.logger.error("فشل حساب نقاط البيفوت: %s", str(e))
            self.pivot_points = {}

    # نظام التريلينغ ستوب المتقدم
    def update_trailing_stop(self, symbol, current_price):
        """
        تحديث مستوى التريلينغ ستوب لعملة معينة حسب أعلى سعر (last_peak) تم الوصول له.
        """
        if symbol not in self.last_peaks or current_price > self.last_peaks[symbol]:
            self.last_peaks[symbol] = current_price

        trailing_stop = self.last_peaks[symbol] * (1 - self.trailing_percent / 100)
        self.trailing_stops[symbol] = trailing_stop
        return trailing_stop

    def evaluate_entry_conditions(self, df, symbol):
        """
        تقييم شروط الدخول باستخدام تحليل متعدد الأطر الزمنية والمعايير المحسنة
        
        الميزات:
        - تحليل متعدد الأطر الزمنية (5m, 15m, 1h)
        - معايير دخول محسنة بناء على backtesting
        - معالجة شاملة للأخطاء
        - تكامل مع نموذج ML للتنبؤ النهائي
        
        Args:
            df: DataFrame يحتوي على بيانات الإطار الزمني 5m
            symbol: رمز العملة المراد تحليلها
            
        Returns:
            bool: True إذا توفرت شروط الدخول، False إذا لم تتوفر
        """
        try:
            # ===== 1. التحقق من صحة البيانات الأساسية =====
            if df is None or len(df) == 0:
                self.logger.warning("بيانات %s فارغة أو غير صالحة", symbol)
                return False

            required_columns = ['ema20', 'ema50', 'rsi', 'macd', 'volume', 'close']
            missing_columns = [col for col in required_columns if col not in df.columns]
            if missing_columns:
                self.logger.warning("أعمدة مفقودة لـ %s: %s", symbol, missing_columns)
                return False

            df_clean = df.dropna(subset=required_columns)
            if df_clean.empty:
                self.logger.warning("بيانات %s تحتوي على قيم فارغة بعد التنظيف", symbol)
                return False

            last = df_clean.iloc[-1]
            
            # ===== 2. تحميل المعايير المحسنة =====
            optimized_params = self.load_optimized_params(symbol)
            params = {
                'rsi_min': optimized_params.get('rsi_min', 50),
                'ema_cross': optimized_params.get('ema_cross', True),
                'macd_condition': optimized_params.get('macd_condition', True),
                'news_threshold': optimized_params.get('news_threshold', 0.2),
                'min_signals': optimized_params.get('min_signals', 1)
            }

            # ===== 3. تحليل متعدد الأطر الزمنية =====
            timeframe_analysis = {}
            try:
                timeframe_analysis = self.analyze_multiple_timeframes(symbol)
                if not timeframe_analysis:
                    self.logger.warning("فشل تحليل الأطر الزمنية لـ %s", symbol)
                    return False
            except Exception as e:
                self.logger.error("خطأ في تحليل الأطر الزمنية لـ %s: %s", symbol, str(e))
                return False

            # ===== 4. تطبيق شروط الدخول =====
            cond_5m = (
                (not params['ema_cross'] or (last['ema20'] > last['ema50'])) and
                (last['rsi'] > params['rsi_min']) and
                (not params['macd_condition'] or (last['macd'] > last['macd_signal']))
            )

            cond_15m = False
            if '15m' in timeframe_analysis:
                try:
                    tf15 = timeframe_analysis['15m']
                    cond_15m = (
                        (tf15['ema20'] > tf15['ema50']) and
                        (tf15['rsi'] > params['rsi_min'])
                    )
                except KeyError as e:
                    self.logger.warning("بيانات إطار 15m ناقصة لـ %s: %s", symbol, str(e))
                    cond_15m = False

            cond_1h = False
            if '1h' in timeframe_analysis:
                try:
                    tf1h = timeframe_analysis['1h']
                    cond_1h = (tf1h['ema20'] > tf1h['ema50'])
                except KeyError as e:
                    self.logger.warning("بيانات إطار 1h ناقصة لـ %s: %s", symbol, str(e))
                    cond_1h = False

            try:
                news_score = self.news_sentiment.get(symbol, {}).get('score', 0)
                signal_count = len(self.pro_signals.get(symbol, []))
                cond_sentiment = (news_score > params['news_threshold']) and \
                                (signal_count >= params['min_signals'])
            except Exception as e:
                self.logger.error("خطأ في تحليل المشاعر لـ %s: %s", symbol, str(e))
                cond_sentiment = False

            final_condition = (
                cond_5m and 
                cond_15m and 
                cond_1h and 
                cond_sentiment
            )

            # ===== 6. التنبؤ باستخدام نموذج ML =====
            if final_condition:
                try:
                    features = [[
                        last['ema20'], last['ema50'], last['rsi'],
                        last['macd'], last['volume'], 
                        news_score, signal_count
                    ]]

                    model = self.load_or_initialize_model(symbol)
                    if model is None:
                        self.logger.warning("النموذج غير متاح لـ %s", symbol)
                        return False

                    input_data = pd.DataFrame(features, columns=[
                        'ema20', 'ema50', 'rsi', 'macd',
                        'volume', 'news_sentiment', 'signal_count'
                    ])

                    prediction = self.safe_model_prediction(model, input_data)
                    return prediction[0] == 1 if prediction is not None else False

                except Exception as e:
                    self.logger.error("فشل التنبؤ لـ %s: %s", symbol, str(e))
                    return False

            return False

        except Exception as e:
            self.logger.critical("فشل غير متوقع في تقييم شروط الدخول لـ %s: %s", symbol, str(e), exc_info=True)
            return False

    def load_or_initialize_model(self, symbol, use_cache=True):
        """
        نسخة محسنة تماماً مع:
        - التحقق من صحة الملف
        - اختبار النموذج قبل التسليم
        - نظام طوارئ متكامل
        """
        try:
            # 1. التحقق من وجود مجلد النماذج
            models_dir = 'models'
            if not os.path.exists(models_dir):
                os.makedirs(models_dir)
                raise FileNotFoundError(f"تم إنشاء مجلد النماذج جديدًا لـ {symbol}")
            
            model_path = os.path.join(models_dir, f'xgb_model_{symbol}.pkl')
            
            # 2. إذا كان النموذج في الذاكرة المؤقتة
            if use_cache and hasattr(self, '_model_cache') and symbol in self._model_cache:
                cached_model = self._model_cache[symbol]
                if self._validate_model(cached_model):
                    return cached_model
            
            # 3. إذا لم يوجد ملف، ننشئ نموذجًا جديدًا
            if not os.path.exists(model_path):
                self.logger.warning("ملف النموذج غير موجود لـ %s، سيتم إنشاء نموذج جديد", symbol)
                new_model = self.train_ml_model(symbol)  # سيحاول تدريب نموذج جديد
                if new_model is None:
                    raise ValueError(f"فشل تدريب نموذج جديد لـ {symbol}")
                return new_model
            
            # 4. تحميل النموذج مع التحقق من صحته
            with open(model_path, 'rb') as f:
                model = joblib.load(f)
            
            if not self._validate_model(model):
                raise ValueError(f"النموذج المحمل لـ {symbol} غير صالح")
            
            # 5. اختبار أداء النموذج
            test_result = self._test_model_performance(model)
            if not test_result['success']:
                raise ValueError(f"أداء النموذج غير مقبول: {test_result['message']}")
            
            # 6. التخزين في الذاكرة المؤقتة إذا طلب
            if use_cache:
                if not hasattr(self, '_model_cache'):
                    self._model_cache = OrderedDict()
                    self._max_cached_models = 3
                
                self._model_cache[symbol] = model
                self._clean_model_cache()
            
            return model
            
        except Exception as e:
            self.logger.error("فشل تحميل/تهيئة النموذج لـ %s: %s", symbol, str(e), exc_info=True)
            raise  # نعيد رفع الاستثناء للتعامل معه في المستوى الأعلى

    def _validate_model(self, model):
        """نسخة محسنة تجمع بين الميزات"""
        # التحقق من الدوال الأساسية
        required_methods = ['predict', 'predict_proba', 'fit']
        for method in required_methods:
            if not hasattr(model, method):
                self.logger.error("النموذج يفتقد إلى الدالة: %s", method)
                return False

        # تحقق إضافي للنماذج من نوع Pipeline
        if hasattr(model, 'steps'):
            last_step = model.steps[-1][1]
            if not hasattr(last_step, 'feature_importances_'):
                self.logger.warning("النموذج قد لا يكون من نوع XGBClassifier")
                # يمكن إضافة إشعار هنا إن أردت

        return True

    @staticmethod
    def _test_model_performance(model):
        """اختبار أداء النموذج على بيانات اختبارية"""
        try:
            # إنشاء بيانات اختبار وهمية
            test_data = pd.DataFrame(np.random.rand(5, 7), columns=[
                'ema20', 'ema50', 'rsi', 'macd',
                'volume', 'news_sentiment', 'signal_count'
            ])

            # الاختبار الأساسي
            predictions = model.predict(test_data)
            if predictions is None or len(predictions) != 5:
                return {
                    'success': False,
                    'message': "فشل في توليد التنبؤات"
                }

            # إذا كان النموذج يحتوي على predict_proba
            if hasattr(model, 'predict_proba'):
                probas = model.predict_proba(test_data)
                if probas is None or not np.all(np.isfinite(probas)):
                    return {
                        'success': False,
                        'message': "قيم احتمالية غير صالحة"
                    }

            return {'success': True, 'message': "النموذج صالح"}

        except Exception as e:
            return {
                'success': False,
                'message': f"فشل اختبار الأداء: {str(e)}"
            }

    def monitor_model_performance(self):
        """مراقبة أداء النماذج بشكل دوري"""
        for symbol, model in self.models.items():
            try:
                # جلب بيانات حديثة للاختبار
                recent_data = self.collect_recent_data(symbol)
                if recent_data is None or recent_data.empty:
                    continue

                # تقييم الأداء
                performance = self.evaluate_model(model, recent_data)

                # إذا كان الأداء تحت عتبة معينة، إعادة التدريب
                if performance['accuracy'] < 0.6:
                    self.logger.warning(
                        "أداء النموذج لـ %s منخفض (%.2f)، سيتم إعادة التدريب",
                        symbol, performance['accuracy']
                    )
                    self.retrain_model(symbol)
            except Exception as e:
                self.logger.error(
                    "فشل مراقبة أداء النموذج لـ %s: %s",
                    symbol, str(e),
                    exc_info=True
                )

    def initialize_and_train_model(self):
        """
        تهيئة نموذج جديد وتدريبه من الصفر بعد التحقق من وجود بيانات التدريب.
        """
        model = Pipeline([
            ('scaler', StandardScaler()),
            ('xgb', XGBClassifier(
                objective='binary:logistic',
                learning_rate=0.1,
                max_depth=6,
                n_estimators=200,
                random_state=42
            ))
        ])

        data_path = 'training_data.csv'
        if not os.path.exists(data_path):
            error_msg = f"❌ ملف بيانات التدريب {data_path} غير موجود. لا يمكن تدريب النموذج."
            self.send_notification('error', error_msg)
            raise FileNotFoundError(error_msg)

        try:
            self.train_ml_model(model)
            return model
        except Exception as e:
            self.send_notification('error', f"❌ فشل في تدريب النموذج الجديد: {e}")
            raise

    def update_training_data(self, symbol, days=90, interval='1h', profit_threshold=0.3):
        """
        جلب بيانات سعرية تاريخية وتحليلها مع إضافة بيانات متعددة الأطر (بدون بيانات المشاعر)

        Parameters:
            symbol: رمز العملة (مثل BTCUSDT)
            days: عدد الأيام التاريخية المطلوبة
            interval: الإطار الزمني الأساسي
            profit_threshold: الحد الأدنى للربح المستهدف

        Returns:
            None (يحفظ البيانات في ملف CSV)
        """
        try:
            # 1. جلب البيانات الأساسية
            klines = self.client.get_historical_klines(symbol, interval, f"{days} day ago UTC")
            if not klines:
                self.send_notification('error', f'⚠️ لم يتم جلب بيانات تاريخية كافية لـ {symbol}.')
                return

            # 2. إنشاء DataFrame الأساسي
            df = pd.DataFrame(klines, columns=[
                'timestamp', 'open', 'high', 'low', 'close', 'volume',
                'close_time', 'quote_asset_volume', 'num_trades',
                'taker_buy_base_vol', 'taker_buy_quote_vol', 'ignore'
            ])
            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            df.set_index('timestamp', inplace=True)
            df = df[['open', 'high', 'low', 'close', 'volume']].astype(float)

            # 3. حساب المؤشرات الفنية للإطار الأساسي
            df['ema20'] = EMAIndicator(df['close'], 20).ema_indicator()
            df['ema50'] = EMAIndicator(df['close'], 50).ema_indicator()
            df['rsi'] = RSIIndicator(df['close'], 14).rsi()
            macd = MACD(df['close'])
            df['macd'] = macd.macd()
            df['macd_signal'] = macd.macd_signal()

            # 4. إضافة بيانات من أطر زمنية أخرى
            try:
                # بيانات 15m
                df_15m = self.get_historical_data(symbol, interval='15m', limit=len(df))
                if df_15m is not None:
                    df_15m = self.calculate_technical_indicators(df_15m)
                    df['15m_rsi'] = df_15m['rsi']
                    df['15m_ema20'] = df_15m['ema20']

                # بيانات 1h
                df_1h = self.get_historical_data(symbol, interval='1h', limit=len(df))
                if df_1h is not None:
                    df_1h = self.calculate_technical_indicators(df_1h)
                    df['1h_ema50'] = df_1h['ema50']
                    df['1h_volume'] = df_1h['volume']

            except Exception as e:
                self.logger.warning("فشل جلب بيانات الأطر الزمنية: %s", str(e))

            # 5. حساب الهدف (Target)
            future_window = 12
            future_price = df['close'].shift(-future_window)
            df['target'] = ((future_price - df['close']) / df['close'] * 100 >= profit_threshold).astype(int)

            # 6. تنظيف البيانات وحفظها
            df.dropna(inplace=True)
            file_path = f"training_data_{symbol}.csv"
            df.to_csv(file_path, index=True)

            self.send_notification('update', f'✅ تم تحديث بيانات التدريب لـ {symbol} وحفظها في {file_path}.')

        except Exception as e:
            self.logger.error("فشل تحديث بيانات التدريب: %s", str(e), exc_info=True)
            self.send_notification('error', f'❌ فشل تحديث بيانات التدريب لـ {symbol}: {e}')

    def validate_system(self):
        """التحقق من صحة جميع المكونات قبل البدء"""
        errors = []
        
        # 1. التحقق من نماذج ML
        for symbol in self.symbols:
            model = self.models.get(symbol)
            if not model:
                errors.append(f"النموذج غير محمل لـ {symbol}")
                
            # اختبار تنبؤ عشوائي
            try:
                dummy_data = pd.DataFrame([[0]*7], columns=[
                    'ema20', 'ema50', 'rsi', 'macd', 
                    'volume', 'news_sentiment', 'signal_count'
                ])
                model.predict(dummy_data)
            except Exception as e:
                errors.append(f"فشل اختبار النموذج لـ {symbol}: {str(e)}")
        
        # 2. التحقق من مصادر الأخبار
        news_sources = ['cryptopanic', 'newsapi']  # المصادر الأساسية
        for source in news_sources:
            if not self.check_news_source(source):
                errors.append(f"مصدر الأخبار {source} غير متاح")
        
        # 3. التحقق من اتصال API
        try:
            self.client.get_account()
        except Exception as e:
            errors.append(f"فشل الاتصال بـ Binance API: {str(e)}")
        
        if errors:
            self.send_notification(
                'error',
                "❌ مشاكل في تهيئة النظام:\n- " + "\n- ".join(errors)
            )
            raise RuntimeError("فشل في التحقق من صحة النظام")

    def train_ml_model(self, symbol):
        """
        تدريب نموذج التعلم الآلي مع ضمانات كاملة ضد الأخطاء
        الميزات:
        1. تحقق شامل من وجود ملف التدريب
        2. معالجة آمنة لجميع مراحل التدريب
        3. تسجيل مفصل لكل خطوة
        4. إشعارات فورية عند المشاكل
        """
        try:
            # 1. التحقق من وجود ملف التدريب
            training_file = f"training_data_{symbol}.csv"
            if not os.path.exists(training_file):
                error_msg = f"ملف التدريب {training_file} غير موجود"
                self.logger.error("%s", error_msg)
                self.send_notification(
                    'error',
                    f"📁 ملف التدريب مفقود\n"
                    f"🪙 {symbol}\n"
                    f"⏰ {datetime.now().strftime('%H:%M')}"
                )
                raise FileNotFoundError(error_msg)

            # 2. تحميل البيانات مع التحقق من الصحة
            try:
                df = pd.read_csv(training_file)
                required_columns = [
                    'ema20', 'ema50', 'rsi', 'macd',
                    'volume', 'news_sentiment', 'signal_count', 'target'
                ]
                
                if not all(col in df.columns for col in required_columns):
                    missing = [col for col in required_columns if col not in df.columns]
                    self.logger.error("أعمدة مفقودة: %s", ', '.join(missing))
                    raise ValueError(f"أعمدة مفقودة: {', '.join(missing)}")

                df = df.dropna(subset=required_columns)
                if len(df) < 100:  # حد أدنى 100 صف للتدريب
                    self.logger.error("بيانات تدريب غير كافية (%d صف فقط)", len(df))
                    raise ValueError(f"بيانات تدريب غير كافية ({len(df)} صف فقط)")

            except Exception as load_error:
                self.logger.error("تحميل بيانات التدريب | %s: %s", type(load_error).__name__, str(load_error), exc_info=True); raise

            # 3. تقسيم البيانات
            try:
                X = df[required_columns[:-1]]  # جميع الأعمدة عدا target
                y = df['target']
                
                X_train, X_test, y_train, y_test = train_test_split(
                    X, y,
                    test_size=0.2,
                    random_state=42,
                    stratify=y
                )
            except Exception as split_error:
                self.logger.error("تقسيم البيانات | %s: %s", type(split_error).__name__, str(split_error), exc_info=True); raise

            # 4. إنشاء وتدريب النموذج
            try:
                model = Pipeline([
                    ('scaler', StandardScaler()),
                    ('xgb', XGBClassifier(
                        objective='binary:logistic',
                        learning_rate=0.1,
                        max_depth=6,
                        n_estimators=200,
                        random_state=42,
                        eval_metric='logloss'
                    ))
                ])
                
                model.fit(X_train, y_train)
            except Exception as train_error:
                self.logger.error("تدريب النموذج | %s: %s", type(train_error).__name__, str(train_error), exc_info=True); raise

            # 5. تقييم النموذج
            try:
                y_pred = model.predict(X_test)
                accuracy = accuracy_score(y_test, y_pred)
                precision = precision_score(y_test, y_pred, zero_division=0)
                recall = recall_score(y_test, y_pred, zero_division=0)
                
                metrics = {
                    'accuracy': round(accuracy, 4),
                    'precision': round(precision, 4),
                    'recall': round(recall, 4),
                    'training_samples': len(X_train),
                    'test_samples': len(X_test)
                }
                
                self.logger.info(
                    "أداء النموذج لـ %s | الدقة: %.4f | الدقة: %.4f | الاسترجاع: %.4f",
                    symbol, metrics['accuracy'], metrics['precision'], metrics['recall']
                )
            except Exception as eval_error:
                self.logger.error("تقييم النموذج | %s: %s", type(eval_error).__name__, str(eval_error), exc_info=True); raise

            # 6. حفظ النموذج
            try:
                model_path = f"xgb_model_{symbol}.pkl"
                joblib.dump(model, model_path)
                
                # التحقق من حفظ الملف
                if not os.path.exists(model_path):
                    raise RuntimeError("فشل حفظ النموذج على القرص")
                    
                self.logger.info("تم حفظ النموذج في %s", model_path)
                
            except Exception as save_error:
                self.logger.error("حفظ النموذج | %s: %s", type(save_error).__name__, str(save_error), exc_info=True); raise

            # 7. إرسال تقرير النجاح
            self.send_notification(
                'report',
                f"🎯 تم تدريب {symbol}\n"
                f"📊 الدقة: {metrics['accuracy']}\n"
                f"🔍 العينات: {metrics['training_samples']} تدريب\n"
                f"⏱ {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            )

            return model

        except FileNotFoundError:
            raise  # نعيد رفع الخطأ للتعامل معه في المستوى الأعلى

        except Exception as e:
            error_msg = f"فشل تدريب النموذج لـ {symbol}: {type(e).__name__}: {str(e)}"
            self.logger.critical("فشل تدريب النموذج لـ %s: %s: %s", symbol, type(e).__name__, str(e), exc_info=True)
            self.send_notification(
                'error',
                f"❌ فشل تدريب {symbol}\n"
                f"📛 {type(e).__name__}\n"
                f"⏰ {datetime.now().strftime('%H:%M')}"
            )
            raise

    def safe_model_prediction(self, model, input_data):
        """تنبؤ آمن مع التحقق من صحة البيانات"""
        try:
            # التحقق من أن input_data هو DataFrame
            if not isinstance(input_data, pd.DataFrame):
                raise TypeError("يجب أن تكون بيانات الإدخال DataFrame")
                
            # التحقق من أسماء الأعمدة
            expected_features = [
                'ema20', 'ema50', 'rsi', 
                'macd', 'volume',
                'news_sentiment', 
                'signal_count'
            ]
            
            missing_features = [f for f in expected_features if f not in input_data.columns]
            if missing_features:
                raise ValueError(f"أعمدة مفقودة: {missing_features}")
            
            # التنبؤ
            return model.predict(input_data[expected_features])
            
        except Exception as e:
            self.send_notification('error', f"فشل التنبؤ: {str(e)}")
            return None

    def record_model_performance(self, model, X, y_true, symbol):
        """تسجيل أداء النموذج مع مقاييس كاملة"""
        try:
            y_pred = model.predict(X)
            
            performance_log = {
                "timestamp": datetime.now().isoformat(),
                "symbol": symbol,
                "accuracy": round(accuracy_score(y_true, y_pred), 4),
                "precision": round(precision_score(y_true, y_pred, zero_division=0), 4),
                "recall": round(recall_score(y_true, y_pred, zero_division=0), 4),
                "features": X.columns.tolist(),
                "model_type": str(model.named_steps['xgb'].__class__.__name__)
            }

            # التسجيل في ملف
            log_path = f'model_performance_{symbol}.json'
            with open(log_path, 'a', encoding='utf-8') as f:
                f.write(json.dumps(performance_log) + '\n')

        except Exception as e:
            self.logger.error("فشل تسجيل أداء النموذج: %s", str(e))

    def get_bot_status(self):
        return {
            'running': self.is_running,
            'start_time': self.start_time,
            'positions': len([p for p in self.current_positions.values() if p]),
            'errors': self.logger.handlers[0].level == logging.ERROR if self.logger.handlers else False
        }

    def _get_system_info(self):
        try:
            return (
                f"🖥 النظام: {platform.system()} {platform.release()}\n"
                f"⏰ وقت التشغيل: {datetime.now() - self.start_time if self.start_time else 'N/A'}\n"
                f"💾 الذاكرة: {psutil.virtual_memory().percent}% مستخدمة"
            )
        except Exception:
            return "معلومات النظام غير متوفرة"

    def append_training_data(self, df, target, symbol):
        """إضافة صف جديد إلى ملف التدريب الخاص بالعملة المحددة"""
        try:
            if df is None or df.empty:
                raise ValueError("DataFrame فارغ أو غير صالح")
                
            last_row = df.iloc[-1]
            
            required_columns = ['ema20', 'ema50', 'rsi', 'macd', 'volume']
            if not all(col in last_row for col in required_columns):
                raise ValueError("أعمدة البيانات المطلوبة مفقودة")
                
            new_data = {
                'timestamp': datetime.utcnow().isoformat(),
                **{col: last_row[col] for col in required_columns},
                'news_sentiment': self.news_sentiment.get(symbol, {}).get('score', 0),
                'signal_count': len(self.pro_signals.get(symbol, [])),
                'target': target
            }
            
            file_path = f'training_data_{symbol}.csv'
            pd.DataFrame([new_data]).to_csv(
                file_path, 
                mode='a', 
                header=not os.path.exists(file_path), 
                index=False
            )
            
        except Exception as e:
            self.send_notification('error', f'فشل في إضافة بيانات التدريب: {str(e)}')
            raise

    def send_notification(self, notification_type, data=None):
        """
        إرسال إشعار آمن مع ضمانات متعددة المستويات
        الميزات:
        1. يعمل بدون توكن تليجرام
        2. يحمي من جميع أنواع الأخطاء
        3. يسجل التفاصيل الكاملة
        4. لا يتوقف التطبيق عند الفشل
        """
        try:
            # 1. التحقق من التهيئة الأساسية
            if not hasattr(self, 'tg_bot') or not hasattr(self.tg_bot, 'token'):
                self._log_failure("لم يتم تهيئة بوت التليجرام", notification_type)
                return False

            # 2. التحقق من نوع الإشعار
            valid_types = {'start', 'shutdown', 'error', 'buy', 'sell', 'report', 'update', 'warning'}
            if notification_type not in valid_types:
                self._log_failure(f"نوع إشعار غير صالح: {notification_type}", notification_type)
                return False

            # 3. إنشاء الرسالة
            try:
                message = self._create_notification_message(notification_type, data or {})
                if not message or len(message) > 4096:
                    raise ValueError("الرسالة غير صالحة")
            except Exception as e:
                self._log_failure(f"فشل إنشاء الرسالة: {str(e)}", notification_type)
                return False

            # 4. تحديد chat_id المناسب
            chat_id = os.getenv(
                'TELEGRAM_DEV_CHAT_ID' if notification_type in {'error', 'warning'} 
                else 'TELEGRAM_GROUP_CHAT_ID'
            )
            if not chat_id:
                self._log_failure("لم يتم تعيين chat_id", notification_type)
                return False

            # 5. محاولة الإرسال
            self.tg_bot.send_message(
                chat_id=chat_id,
                text=message,
                parse_mode=telegram.constants.ParseMode.MARKDOWN,
            )
            return True

        except telegram.error.InvalidToken:
            self._log_failure("توكن تليجرام غير صالح", notification_type)
        except telegram.error.TelegramError as e:
            self._log_failure(f"خطأ تليجرام: {str(e)}", notification_type)
        except Exception as e:
            self._log_failure(f"فشل غير متوقع: {str(e)}", notification_type)
        
        return False

    def _log_error(self, error_msg, emergency_prefix=""):
        """
        نسخة محسنة تسجل الأخطاء بكل السيناريوهات
        - تعمل مع أو بدون logger
        - تكتب في ملف طوارئ إذا لزم الأمر
        - تضيف بادئة طوارئ إذا كانت متوفرة
        """
        full_msg = f"{emergency_prefix}{error_msg}" if emergency_prefix else error_msg
        
        try:
            if hasattr(self, 'logger') and self.logger.handlers:
                self.logger.error(full_msg)
            else:
                # نظام الطوارئ المتدرج
                try:
                    with open('emergency_errors.log', 'a', encoding='utf-8') as f:
                        f.write(f"[{datetime.now()}] {full_msg}\n")
                except Exception as e:
                    print(f"[FALLBACK] {full_msg} | Exception: {str(e)}")
        except Exception as e:
            print(f"[CRITICAL] فشل تسجيل الخطأ: {str(e)} | الرسالة الأصلية: {error_msg}")

    def _safe_send_to_telegram(self, chat_id, message, notification_type, max_retries=3):
        """إرسال آمن مع جميع الضمانات"""
        for attempt in range(max_retries):
            try:
                if not all([chat_id, message, notification_type]):
                    raise ValueError("مدخلات إرسال غير صالحة")

                self.tg_bot.send_message(
                    chat_id=chat_id,
                    text=message,
                    parse_mode=ParseMode.MARKDOWN,
                    disable_web_page_preview=True
                )
                return True

            except telegram.error.RetryAfter as e:
                wait_time = e.retry_after + 2
                time.sleep(wait_time)
                continue

            except telegram.error.TelegramError as tg_error:
                error_msg = f"خطأ في التليجرام (المحاولة {attempt + 1}): {str(tg_error)}"
                self._log_error(error_msg)
                if attempt == max_retries - 1:
                    self._emergency_log_notification('telegram_failure', error_msg)
                time.sleep(2 ** attempt)
                continue

            except Exception as e:
                error_msg = f"فشل إرسال غير متوقع (المحاولة {attempt + 1}): {str(e)}"
                self._log_error(error_msg)
                if attempt == max_retries - 1:
                    self._emergency_log_notification('send_failure', error_msg)
                time.sleep(1)
                continue

        return False

    def _emergency_log_notification(self, error_type, error_details):
        """نظام طوارئ متكامل"""
        try:
            log_entry = {
                'timestamp': datetime.now().isoformat(),
                'type': error_type,
                'details': error_details,
                'bot_status': {
                    'running': getattr(self, 'is_running', False),
                    'positions': len(getattr(self, 'current_positions', []))
                }
            }

            try:
                with open('notification_errors.jsonl', 'a', encoding='utf-8') as f:
                    f.write(json.dumps(log_entry, ensure_ascii=False) + '\n')
            except Exception:
                with open('notification_errors.log', 'a', encoding='utf-8') as f:
                    f.write(f"{log_entry['timestamp']} | {error_type} | {error_details}\n")

        except Exception as e:
            print(f"EMERGENCY: {error_type} - {error_details} | {str(e)}")

    def _create_notification_message(self, notification_type, data):
        """إنشاء محتوى الرسالة بناءً على نوع الإشعار"""
        messages = {
            'start': "✅ **تم تشغيل البوت بنجاح**\n" + self._get_system_info(),
            'shutdown': f"🛑 **تم إيقاف البوت**\nالسبب: {data.get('reason', 'غير معروف')}",
            'connection': f"🌐 **حالة الاتصال**: {data.get('status', 'انقطع الاتصال')}",
            'buy': (
                f"🚀 **شراء جديد**\n"
                f"🪙 العملة: {data.get('symbol', 'N/A')}\n"
                f"📊 الكمية: {data.get('quantity', 'N/A')}\n"
                f"💰 السعر: {data.get('price', 'N/A')}\n"
                f"💵 الاستثمار: {data.get('investment', 'N/A')}"
            ),
            'sell': (
                f"💰 **إغلاق صفقة**\n"
                f"🪙 العملة: {data.get('symbol', 'N/A')}\n"
                f"📊 الكمية: {data.get('quantity', 'N/A')}\n"
                f"💰 سعر البيع: {data.get('price', 'N/A')}\n"
                f"📈 الربح: {data.get('profit', 'N/A')}%\n"
                f"⏱ المدة: {data.get('duration', 'N/A')}"
            ),
            'error': f"❌ **خطأ**: {data if isinstance(data, str) else str(data)}",
            'report': (
                f"📊 **تقرير أداء**\n"
                f"📈 الإشارات النشطة: {data.get('active_signals', 0)}\n"
                f"🔮 التوقع: {data.get('prediction', 'N/A')}"
            )
        }
        
        return messages.get(notification_type, f"🔔 إشعار غير معروف: {notification_type}")

    def _send_to_telegram(self, notification_type, message):
        """إرسال فعلي عبر التليجرام"""
        chat_id = os.getenv('TELEGRAM_PRIVATE_CHAT_ID' if notification_type in ['start', 'shutdown', 'error', 'connection'] else 'TELEGRAM_GROUP_CHAT_ID')
        self.tg_bot.send_message(
            chat_id=chat_id,
            text=message,
            parse_mode=ParseMode.MARKDOWN
        )

    def _safe_send_message(self, chat_id, message, retries=3):
        """إرسال آمن مع إعادة محاولة"""
        for attempt in range(retries):
            try:
                self.tg_bot.send_message(
                    chat_id=chat_id,
                    text=message,
                    parse_mode=ParseMode.MARKDOWN,
                  
                )
                return
            except NetworkError:
                if attempt == retries - 1:
                    raise
                time.sleep(5)

    def run(self):
        """الدورة الرئيسية المحدثة مع التحليل الزمني وإدارة الأخطاء المتكاملة"""
        try:
            # 1. تهيئة الجدولة الأساسية
            schedule.every(15).minutes.do(self.generate_performance_report)
            schedule.every(1).hours.do(self.rotate_data_sources)
            schedule.every().day.at("02:00").do(self.retrain_model)
            schedule.every().sunday.at("02:30").do(
                lambda: [
                    self.optimize_entry_conditions(symbol)
                    for symbol in self.symbols
                ]
            )
            
            # 2. جدولة التحليل الزمني الأسبوعي (إضافة جديدة)
            schedule.every().monday.at("03:00").do(
                self.analyze_market_timing
            )
            
            self.start_bot()
            
            # 3. بدء جدولة المهام في خلفية thread منفصل
            self.start_scheduler()

            while self.is_running:
                try:
                    # 4. التحقق من الاتصال بالإنترنت
                    if not self.check_internet_connection():
                        self.handle_connection_loss()
                        continue

                    # 5. تطبيق التحليل الزمني في قرارات التداول (إضافة جديدة)
                    current_hour = datetime.now().hour
                    use_aggressive = current_hour in self.optimal_trading_hours
                    
                    # 6. معالجة كل عملة في thread منفصل مع تطبيق الإعدادات المناسبة
                    threads = []
                    for symbol in self.symbols:
                        thread = threading.Thread(
                            target=self._process_coin_with_strategy,
                            args=(symbol, use_aggressive),
                            daemon=True
                        )
                        threads.append(thread)
                        thread.start()

                    # 7. انتظار انتهاء جميع threads
                    for thread in threads:
                        thread.join(timeout=300)  # مهلة 5 دقائق لكل thread

                    # 8. إدارة المراكز المفتوحة
                    self.manage_all_positions()

                    # 9. فاصل زمني بين الدورات
                    time.sleep(60)

                except Exception as e:
                    self.logger.critical("خطأ في الدورة الرئيسية: %s", str(e), exc_info=True)
                    time.sleep(30)  # انتظار 30 ثانية قبل إعادة المحاولة

        except Exception as e:
            self.logger.error("انهيار في دالة run: %s", str(e), exc_info=True)
            self.shutdown_bot(reason=f"خطأ حرج: {type(e).__name__}")
