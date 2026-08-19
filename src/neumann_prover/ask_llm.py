"""Public entry point for invoking language models.

`ask_llm` resolves a model (explicit id, stage default, or the cheap fallback),
infers the provider, and delegates to the matching adapter.
"""
from __future__ import annotations

from typing import Optional

from .stages import STAGE_DEFAULTS, OPENAI_CHEAP
from .providers import _ask_openai, _ask_anthropic, _ask_together, _provider_for


def ask_llm(
    text: str,
    *,
    stage: Optional[str] = None,
    model: Optional[str] = None,
    temperature: Optional[float] = None,
) -> str:
    """Generate text with an explicit `model`, a `stage` default, or the cheap
    fallback. `temperature` is only forwarded to models that accept it (see
    providers._accepts_temperature); leave it None for gpt-5 / Opus 4.7+."""
    if model is not None:
        target = model
    elif stage is not None:
        try:
            target = STAGE_DEFAULTS[stage]
        except KeyError:
            raise ValueError(
                f"Unknown stage '{stage}'. Valid: {tuple(STAGE_DEFAULTS)}"
            ) from None
    else:
        target = OPENAI_CHEAP

    provider = _provider_for(target)
    if provider == "openai":
        return _ask_openai(target, text, temperature=temperature)
    if provider == "anthropic":
        return _ask_anthropic(target, text, temperature=temperature)
    return _ask_together(target, text, temperature=temperature)
