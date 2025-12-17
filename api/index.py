"""
Vercel serverless function entry point for Neumann Prover web interface.
This file adapts the FastAPI app to work with Vercel's serverless functions.
"""
import sys
from pathlib import Path

# Add src directory to path so imports work
src_path = Path(__file__).parent.parent / "src"
sys.path.insert(0, str(src_path))

from neumann_prover.web_app import app

# Vercel expects a handler function
handler = app
