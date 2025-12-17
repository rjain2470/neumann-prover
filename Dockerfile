# Dockerfile for Neumann Prover Web Interface
FROM python:3.11-slim

# Set working directory
WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    bash \
    && rm -rf /var/lib/apt/lists/*

# Install Lean and elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
ENV PATH="/root/.elan/bin:${PATH}"

# Copy project files
COPY . /app

# Install Python dependencies
RUN pip install --no-cache-dir -e .

# Setup Lean environment
RUN bash scripts/setup_lean_env.sh || true

# Expose port
EXPOSE 8000

# Set environment variable for Lean project
ENV NEUMANN_LEAN_PROJECT=/app/lean_project

# Run the web server
CMD ["python", "-m", "uvicorn", "neumann_prover.web_app:app", "--host", "0.0.0.0", "--port", "8000"]
