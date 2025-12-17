"""
src/neumann_prover/web_app.py

FastAPI web server for the Neumann Prover autoformalization tool.
Provides a REST API and WebSocket endpoints for the web interface.
"""

from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles
from fastapi.responses import HTMLResponse, JSONResponse
from pydantic import BaseModel, Field
from typing import Optional, Dict, List, Any, Literal
import asyncio
import json
import os
from pathlib import Path

# Import neumann_prover modules
from neumann_prover import stages, list_stages, default_model_for
from neumann_prover.providers import _provider_for
from neumann_prover.pipelines.batch import run_pipeline
from neumann_prover.utils import compile_lean_snippet, extract_lean_code, ensure_import_mathlib
from neumann_prover.correction import formal_statement_until_compiles, try_formal_proof_until_compiles
from neumann_prover.pipelines.informal import informal_proof_generator, lean_pseudocode_generator
from neumann_prover.pipelines.formal_statement import formal_statement_generator
from neumann_prover.pipelines.formal_proof import formal_proof_generator


# Create FastAPI app
app = FastAPI(
    title="Neumann Prover API",
    description="End-to-end autoformalization API for mathematical proofs in Lean",
    version="0.1.0"
)

# CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # In production, restrict this to specific origins
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Pydantic models for API requests/responses
class StagesResponse(BaseModel):
    """Response model for stages endpoint"""
    stages: Dict[str, str] = Field(..., description="Mapping of stage names to default models")
    stage_list: List[str] = Field(..., description="List of valid stage names")


class ModelsResponse(BaseModel):
    """Response model for models endpoint"""
    models: Dict[str, List[str]] = Field(..., description="Available models by provider")
    all_models: List[str] = Field(..., description="All available model identifiers")


class GenerateRequest(BaseModel):
    """Request model for generate endpoint"""
    informal_statement: str = Field(..., description="Informal mathematical statement")
    informal_proof: Optional[str] = Field(None, description="Optional informal proof")
    formal_statement: Optional[str] = Field(None, description="Optional formal statement in Lean")
    lean_pseudocode: Optional[str] = Field(None, description="Optional Lean pseudocode")
    previous_errors: Optional[str] = Field(None, description="Previous compiler errors for correction mode")
    
    # Output configuration
    generate_informal_proof: bool = Field(True, description="Generate informal proof")
    generate_formal_statement: bool = Field(True, description="Generate formal statement")
    generate_formal_proof: bool = Field(True, description="Generate formal proof")
    generate_pseudocode: bool = Field(True, description="Generate Lean pseudocode")
    
    # Model selection (None = use defaults)
    model_informal: Optional[str] = Field(None, description="Model for informal proof generation")
    model_statement: Optional[str] = Field(None, description="Model for formal statement generation")
    model_proof: Optional[str] = Field(None, description="Model for formal proof generation")
    
    # Advanced settings
    temperature: float = Field(0.7, ge=0.0, le=1.0, description="Model temperature")
    max_statement_iters: int = Field(3, ge=1, le=10, description="Max correction iterations for statement")
    max_proof_iters: int = Field(4, ge=1, le=10, description="Max correction iterations for proof")
    project_root: Optional[str] = Field(None, description="Custom Lean project path")


class CompileRequest(BaseModel):
    """Request model for compile endpoint"""
    lean_code: str = Field(..., description="Lean code to compile")
    project_root: Optional[str] = Field(None, description="Custom Lean project path")
    filename: str = Field("Main.lean", description="Filename for compilation")


class CompileResponse(BaseModel):
    """Response model for compile endpoint"""
    success: bool = Field(..., description="Whether compilation succeeded")
    stdout: str = Field(..., description="Compiler stdout")
    stderr: str = Field(..., description="Compiler stderr")
    code: str = Field(..., description="Processed Lean code")


class HealthResponse(BaseModel):
    """Response model for health endpoint"""
    status: str = Field(..., description="Service status")
    lean_available: bool = Field(..., description="Whether Lean toolchain is available")
    environment_vars: Dict[str, bool] = Field(..., description="API key environment variable status")


# WebSocket connection manager
class ConnectionManager:
    def __init__(self):
        self.active_connections: List[WebSocket] = []

    async def connect(self, websocket: WebSocket):
        await websocket.accept()
        self.active_connections.append(websocket)

    def disconnect(self, websocket: WebSocket):
        self.active_connections.remove(websocket)

    async def send_personal_message(self, message: dict, websocket: WebSocket):
        await websocket.send_json(message)

    async def broadcast(self, message: dict):
        for connection in self.active_connections:
            try:
                await connection.send_json(message)
            except:
                pass


manager = ConnectionManager()


# Mount static files
static_dir = Path(__file__).parent / "static"
if static_dir.exists():
    app.mount("/static", StaticFiles(directory=str(static_dir)), name="static")


# API Endpoints
@app.get("/", response_class=HTMLResponse)
async def root():
    """Serve the main web interface"""
    index_file = static_dir / "index.html"
    
    if index_file.exists():
        return HTMLResponse(content=index_file.read_text(), status_code=200)
    else:
        return HTMLResponse(
            content="<h1>Neumann Prover API</h1><p>Frontend not found. Please access the API directly at /docs</p>",
            status_code=200
        )


@app.get("/api/stages", response_model=StagesResponse)
async def get_stages():
    """
    Get all available pipeline stages and their default models.
    Dynamically loads from stages.py configuration.
    """
    return StagesResponse(
        stages=stages.STAGE_DEFAULTS,
        stage_list=list_stages()
    )


@app.get("/api/models", response_model=ModelsResponse)
async def get_models():
    """
    Get all available models organized by provider.
    """
    # Extract model constants from stages module
    openai_models = [
        stages.OPENAI_STRONG,
        stages.OPENAI_BUDGET,
        stages.OPENAI_CHEAP,
    ]
    
    anthropic_models = [
        stages.ANTHROPIC_BAL,
        stages.ANTHROPIC_STRG,
    ]
    
    # Common Together AI models (examples - can be expanded)
    together_models = [
        "meta-llama/Llama-3-70b-chat-hf",
        "meta-llama/Llama-3-8b-chat-hf",
        "deepseek-ai/deepseek-coder-33b-instruct",
        "Qwen/Qwen2-72B-Instruct",
    ]
    
    all_models = openai_models + anthropic_models + together_models
    
    return ModelsResponse(
        models={
            "openai": openai_models,
            "anthropic": anthropic_models,
            "together": together_models,
        },
        all_models=all_models
    )


@app.post("/api/generate")
async def generate(request: GenerateRequest):
    """
    Main generation pipeline endpoint.
    Processes the request and returns generated artifacts.
    """
    try:
        # Prepare input for run_pipeline
        input_data = {
            "informal_text": request.informal_statement,
        }
        
        # Add optional inputs if provided
        if request.informal_proof:
            input_data["informal_proof"] = request.informal_proof
        if request.formal_statement:
            input_data["formal_statement"] = request.formal_statement
        if request.lean_pseudocode:
            input_data["pseudocode"] = request.lean_pseudocode
        
        # Run the pipeline
        result = run_pipeline(
            informal_inputs=[input_data],
            output_informal_proofs=request.generate_informal_proof,
            output_formal_statements=request.generate_formal_statement,
            output_pseudocode=request.generate_pseudocode,
            model_informal=request.model_informal,
            model_statement=request.model_statement,
            model_proof=request.model_proof,
            num_statement_iters=request.max_statement_iters,
            num_proof_iters=request.max_proof_iters,
            interactive=False,
            run_full_pipeline=True,
        )
        
        # Extract the first (and only) item from results
        if result["items"]:
            item = result["items"][0]
            
            # Format response
            response = {
                "success": True,
                "informal_proof": item.get("informal_proof"),
                "pseudocode": item.get("pseudocode"),
                "formal_statement": item.get("formal_statement"),
                "formal_proof": item.get("formal_proof"),
                "summary": result.get("summary"),
                "config": result.get("config"),
            }
            
            return JSONResponse(content=response)
        else:
            raise HTTPException(status_code=500, detail="Pipeline produced no results")
            
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Generation error: {str(e)}")


@app.post("/api/compile", response_model=CompileResponse)
async def compile_code(request: CompileRequest):
    """
    Standalone Lean compilation check.
    """
    try:
        code = ensure_import_mathlib(extract_lean_code(request.lean_code))
        ok, stdout, stderr = compile_lean_snippet(
            code,
            project_root=request.project_root,
            filename=request.filename
        )
        
        return CompileResponse(
            success=ok,
            stdout=stdout,
            stderr=stderr,
            code=code
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Compilation error: {str(e)}")


@app.get("/api/health", response_model=HealthResponse)
async def health_check():
    """
    System health and dependency check.
    """
    # Check if Lean is available
    lean_available = False
    try:
        ok, _, _ = compile_lean_snippet("import Mathlib\n\ntheorem test : True := trivial\n")
        lean_available = ok
    except:
        pass
    
    # Check environment variables (don't expose actual values)
    env_vars = {
        "OPENAI_API_KEY": bool(os.getenv("OPENAI_API_KEY")),
        "ANTHROPIC_API_KEY": bool(os.getenv("ANTHROPIC_API_KEY")),
        "TOGETHER_API_KEY": bool(os.getenv("TOGETHER_API_KEY")),
    }
    
    return HealthResponse(
        status="healthy",
        lean_available=lean_available,
        environment_vars=env_vars
    )


@app.websocket("/ws/progress")
async def websocket_endpoint(websocket: WebSocket):
    """
    WebSocket endpoint for real-time progress updates.
    Clients can connect here to receive updates during long-running operations.
    """
    await manager.connect(websocket)
    try:
        while True:
            # Keep connection alive and receive any client messages
            data = await websocket.receive_text()
            
            # Echo back for testing
            await manager.send_personal_message(
                {"type": "echo", "message": data},
                websocket
            )
    except WebSocketDisconnect:
        manager.disconnect(websocket)


# For development/testing
if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
