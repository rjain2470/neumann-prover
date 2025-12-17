#!/bin/bash
# Startup script for Neumann Prover Web Interface

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${BLUE}╔════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  Neumann Prover Web Interface Startup ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════╝${NC}"
echo ""

# Check if Python is installed
if ! command -v python &> /dev/null; then
    echo -e "${YELLOW}Error: Python is not installed.${NC}"
    exit 1
fi

# Check if package is installed
if ! python -c "import neumann_prover" 2>/dev/null; then
    echo -e "${YELLOW}Installing Neumann Prover package...${NC}"
    pip install -e . > /dev/null 2>&1
    echo -e "${GREEN}✓ Package installed${NC}"
fi

# Check for API keys (optional)
echo -e "${BLUE}Checking API key configuration...${NC}"
if [ -z "$OPENAI_API_KEY" ] && [ -z "$ANTHROPIC_API_KEY" ] && [ -z "$TOGETHER_API_KEY" ]; then
    echo -e "${YELLOW}⚠ Warning: No API keys found in environment variables.${NC}"
    echo -e "${YELLOW}  You can set them in the web interface or export them:${NC}"
    echo -e "${YELLOW}    export OPENAI_API_KEY='your-key'${NC}"
    echo -e "${YELLOW}    export ANTHROPIC_API_KEY='your-key'${NC}"
    echo -e "${YELLOW}    export TOGETHER_API_KEY='your-key'${NC}"
    echo ""
else
    echo -e "${GREEN}✓ API keys detected${NC}"
fi

# Check if Lean is installed (optional)
if command -v lean &> /dev/null; then
    echo -e "${GREEN}✓ Lean toolchain detected${NC}"
else
    echo -e "${YELLOW}⚠ Warning: Lean toolchain not found.${NC}"
    echo -e "${YELLOW}  Run 'bash scripts/setup_lean_env.sh' to install it.${NC}"
    echo ""
fi

# Set default port
PORT=${1:-8000}

# Start the server
echo -e "${GREEN}Starting web server on port ${PORT}...${NC}"
echo -e "${BLUE}Access the interface at: ${GREEN}http://localhost:${PORT}${NC}"
echo -e "${BLUE}API documentation at: ${GREEN}http://localhost:${PORT}/docs${NC}"
echo ""
echo -e "${YELLOW}Press CTRL+C to stop the server${NC}"
echo ""

python -m uvicorn neumann_prover.web_app:app --host 0.0.0.0 --port ${PORT} --reload
