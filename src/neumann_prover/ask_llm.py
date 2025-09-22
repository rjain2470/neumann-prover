
'''
src/neumann_prover/ask_llm.py

This module is the public entry point for invoking language models. It selects a model by explicit identifier or by stage default, infers the provider, and delegates the call to the provider adapter.

Functions:

ask_llm(text: str, *, stage: str | None = None, model: str | None = None, temperature: float = 0.2) -> str
Input: a prompt, optional stage or explicit model identifier, and temperature. Output: model response as plain text.

_ask_together_provider_for(model: str) -> str
Input: a model identifier. Output: provider name inferred from the identifier (compatibility alias).
'''

import os
from typing import Optional
from .stages import list_stages, default_model_for, STAGE_DEFAULTS, VALID_STAGES, OPENAI_CHEAP
from .providers import _ask_openai, _ask_anthropic, _ask_together, _provider_for

def ask_llm(
    text: str,
    *,
    stage: Optional[str] = None,
    model: Optional[str] = None,
    temperature: float = 1,
) -> str:
    """
    Use a stage default or explicit model to generate output.
    Stages:
      informal_proof
      formal_statement_draft
      formal_proof_draft
      formal_statement_correction
      formal_proof_correction
    """
    if model is None:
        if stage is None:
            target = OPENAI_CHEAP
        else:
            if stage not in STAGE_DEFAULTS:
                raise ValueError(f"Unknown stage '{stage}'. Valid: {VALID_STAGES}")
            target = STAGE_DEFAULTS[stage]
    else:
        target = model

    provider = _provider_for(target)
    if provider == "openai":
        return _ask_openai(target, text, temperature=temperature)
    if provider == "anthropic":
        return _ask_anthropic(target, text, temperature=temperature)
    return _ask_together(target, text, temperature=temperature)
