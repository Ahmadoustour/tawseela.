FROM python:3.10-slim

# إعداد بيئة العمل
WORKDIR /app

# نسخ المتطلبات وتثبيتها
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# نسخ باقي الملفات
COPY . .

# عند التشغيل، بافتراض Akash يطبق ulimit
CMD ["python", "bot.py"]
