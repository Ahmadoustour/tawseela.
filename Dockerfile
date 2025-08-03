FROM python:3.10-slim

# إعدادات
WORKDIR /app

# نسخ المتطلبات
COPY requirements.txt .

# تثبيت الحزم
RUN pip install --no-cache-dir -r requirements.txt

# نسخ باقي الملفات
COPY . .

# أمر التشغيل
CMD ["python", "bot.py"]
