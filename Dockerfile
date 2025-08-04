FROM python:3.10-slim

# زيادة حدود الملفات
RUN echo "fs.inotify.max_user_watches=524288" >> /etc/sysctl.conf \
    && echo "* soft nofile 65536" >> /etc/security/limits.conf \
    && echo "* hard nofile 65536" >> /etc/security/limits.conf

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

CMD ["python", "bot.py"]
