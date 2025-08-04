FROM python:3.10-slim

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

# استخدم sh -c لتطبيق ulimit ثم تشغيل البوت
ENTRYPOINT ["sh", "-c", "ulimit -n 65536 && exec python bot.py"]
