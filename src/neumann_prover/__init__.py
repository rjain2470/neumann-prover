
'''
src/neumann_prover/init.py

This package initializer exposes the most common entry points so users can import from neumann_prover directly.

Exports:
ask_llm: main text-to-model dispatcher (from ask_llm.py).
list_stages: list of valid pipeline stages (from stages.py).
default_model_for: default model identifier for a stage (from stages.py).
'''


from .ask_llm import ask_llm
from .stages import list_stages, default_model_for

# Import directly from submodules to avoid relying on pipelines/__init__.py
from .pipelines.informal import (
    informal_proof_generator,
    lean_pseudocode_generator,
)
from .pipelines.formal_statement import formal_statement_generator
from .pipelines.formal_proof import formal_proof_generator
from .pipelines.batch import run_pipeline

__all__ = [
    "ask_llm",
    "list_stages",
    "default_model_for",
    "informal_proof_generator",
    "lean_pseudocode_generator",
    "formal_statement_generator",
    "formal_proof_generator",
    "run_pipeline",
]
