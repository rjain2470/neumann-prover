# Neumann Prover Web API Documentation

## Overview

The Neumann Prover Web API provides a REST interface for mathematical autoformalization, allowing you to generate formal proofs in Lean from informal mathematical statements.

## Base URL

When running locally:
```
http://localhost:8000
```

## Authentication

API keys are managed client-side in the web interface. For programmatic access, ensure the following environment variables are set on the server:
- `OPENAI_API_KEY`
- `ANTHROPIC_API_KEY`
- `TOGETHER_API_KEY`

## Endpoints

### GET /api/stages

Get all available pipeline stages and their default models. This endpoint dynamically loads configuration from the `stages.py` module.

**Response 200 (application/json)**

```json
{
  "stages": {
    "informal_proof": "gpt-5-mini",
    "formal_statement_draft": "gpt-5-mini",
    "formal_proof_draft": "gpt-5",
    "formal_statement_correction": "gpt-5-mini",
    "formal_proof_correction": "gpt-5-mini",
    "formal_statement": "gpt-5-mini",
    "formal_proof": "gpt-5-mini"
  },
  "stage_list": [
    "informal_proof",
    "formal_statement_draft",
    "formal_proof_draft",
    "formal_statement_correction",
    "formal_proof_correction",
    "formal_statement",
    "formal_proof"
  ]
}
```

### GET /api/models

Get all available models organized by provider.

**Response 200 (application/json)**

```json
{
  "models": {
    "openai": ["gpt-5", "gpt-5-mini", "gpt-5-nano"],
    "anthropic": ["claude-opus-4-1-20250805", "claude-sonnet-4-20250514"],
    "together": [
      "meta-llama/Llama-3-70b-chat-hf",
      "meta-llama/Llama-3-8b-chat-hf",
      "deepseek-ai/deepseek-coder-33b-instruct",
      "Qwen/Qwen2-72B-Instruct"
    ]
  },
  "all_models": ["gpt-5", "gpt-5-mini", ...]
}
```

### POST /api/generate

Main generation pipeline endpoint. Processes mathematical statements and generates proofs.

**Request Body (application/json)**

```json
{
  "informal_statement": "For every even integer n, 4 divides n^2.",
  "informal_proof": null,
  "formal_statement": null,
  "lean_pseudocode": null,
  "previous_errors": null,
  "generate_informal_proof": true,
  "generate_formal_statement": true,
  "generate_formal_proof": true,
  "generate_pseudocode": true,
  "model_informal": null,
  "model_statement": null,
  "model_proof": null,
  "temperature": 0.7,
  "max_statement_iters": 3,
  "max_proof_iters": 4,
  "project_root": null
}
```

**Parameters**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| informal_statement | string | Yes | - | Informal mathematical statement |
| informal_proof | string | No | null | Optional informal proof |
| formal_statement | string | No | null | Optional formal statement in Lean |
| lean_pseudocode | string | No | null | Optional Lean pseudocode |
| previous_errors | string | No | null | Previous compiler errors for correction mode |
| generate_informal_proof | boolean | No | true | Generate informal proof |
| generate_formal_statement | boolean | No | true | Generate formal statement |
| generate_formal_proof | boolean | No | true | Generate formal proof |
| generate_pseudocode | boolean | No | true | Generate Lean pseudocode |
| model_informal | string | No | null | Model for informal proof (null = use default) |
| model_statement | string | No | null | Model for formal statement (null = use default) |
| model_proof | string | No | null | Model for formal proof (null = use default) |
| temperature | float | No | 0.7 | Model temperature (0.0-1.0) |
| max_statement_iters | integer | No | 3 | Max correction iterations for statement (1-10) |
| max_proof_iters | integer | No | 4 | Max correction iterations for proof (1-10) |
| project_root | string | No | null | Custom Lean project path |

**Response 200 (application/json)**

```json
{
  "success": true,
  "informal_proof": {
    "text": "If n is even, then n = 2k for some integer k. Then n² = (2k)² = 4k², which is divisible by 4."
  },
  "pseudocode": {
    "text": "intro n h\nrcases h with ⟨k, hk⟩\nrefine ⟨k^2, ?_⟩\n..."
  },
  "formal_statement": {
    "text": "import Mathlib\n\nnamespace Demo\n\ntheorem even_square_div_four : ∀ n : ℤ, Even n → 4 ∣ n^2 := by\n  sorry\n\nend Demo",
    "compiled": true,
    "stdout": "Main.lean:5:8: warning: declaration uses 'sorry'",
    "stderr": ""
  },
  "formal_proof": {
    "text": "import Mathlib\n\nnamespace Demo\n\ntheorem even_square_div_four : ∀ n : ℤ, Even n → 4 ∣ n^2 := by\n  intro n ⟨k, hk⟩\n  refine ⟨k^2, ?_⟩\n  calc n^2 = (2*k)^2 := by rw [hk]\n       _ = 4*k^2 := by ring\n\nend Demo",
    "compiled": true,
    "stdout": "",
    "stderr": ""
  },
  "summary": {
    "n_items": 1,
    "statements_compiled": 1,
    "proofs_compiled": 1,
    "elapsed_sec": 45.234
  },
  "config": {
    "output_informal_proofs": true,
    "output_formal_statements": true,
    "output_pseudocode": true,
    "model_informal": "gpt-5-mini",
    "model_statement": "gpt-5-mini",
    "model_proof": "gpt-5",
    "num_statement_iters": 3,
    "num_proof_iters": 4
  }
}
```

**Response 500 (application/json)**

```json
{
  "detail": "Generation error: <error message>"
}
```

### POST /api/compile

Standalone Lean compilation check. Validates Lean code without running the full generation pipeline.

**Request Body (application/json)**

```json
{
  "lean_code": "import Mathlib\n\ntheorem test : True := trivial",
  "project_root": null,
  "filename": "Main.lean"
}
```

**Parameters**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| lean_code | string | Yes | - | Lean code to compile |
| project_root | string | No | null | Custom Lean project path |
| filename | string | No | "Main.lean" | Filename for compilation |

**Response 200 (application/json)**

```json
{
  "success": true,
  "stdout": "",
  "stderr": "",
  "code": "import Mathlib\n\ntheorem test : True := trivial\n"
}
```

### GET /api/health

System health and dependency check. Returns the status of the API server and available dependencies.

**Response 200 (application/json)**

```json
{
  "status": "healthy",
  "lean_available": true,
  "environment_vars": {
    "OPENAI_API_KEY": true,
    "ANTHROPIC_API_KEY": false,
    "TOGETHER_API_KEY": true
  }
}
```

**Response Fields**

- `status`: Always "healthy" if server is running
- `lean_available`: Whether the Lean toolchain is installed and accessible
- `environment_vars`: Boolean flags indicating which API keys are configured (does not expose actual key values)

### WebSocket /ws/progress

Real-time progress updates during generation. Connect to this endpoint to receive live updates about ongoing operations.

**Connection**

```javascript
const ws = new WebSocket('ws://localhost:8000/ws/progress');

ws.onmessage = (event) => {
  const data = JSON.parse(event.data);
  console.log('Progress update:', data);
};
```

**Message Format**

```json
{
  "type": "progress",
  "stage": "formal_proof_draft",
  "percentage": 75,
  "message": "Generating formal proof..."
}
```

## Usage Examples

### Python

```python
import requests

# Generate a proof
response = requests.post('http://localhost:8000/api/generate', json={
    'informal_statement': 'For every even integer n, 4 divides n^2.',
    'generate_informal_proof': True,
    'generate_formal_statement': True,
    'generate_formal_proof': True,
    'max_statement_iters': 3,
    'max_proof_iters': 4
})

result = response.json()
if result['success']:
    print('Formal proof:', result['formal_proof']['text'])
    print('Compiled:', result['formal_proof']['compiled'])
```

### cURL

```bash
# Get available stages
curl http://localhost:8000/api/stages

# Generate a proof
curl -X POST http://localhost:8000/api/generate \
  -H "Content-Type: application/json" \
  -d '{
    "informal_statement": "For every even integer n, 4 divides n^2.",
    "generate_informal_proof": true,
    "generate_formal_statement": true,
    "generate_formal_proof": true,
    "max_statement_iters": 3,
    "max_proof_iters": 4
  }'

# Check health
curl http://localhost:8000/api/health
```

### JavaScript/Fetch

```javascript
// Generate a proof
const response = await fetch('http://localhost:8000/api/generate', {
  method: 'POST',
  headers: {
    'Content-Type': 'application/json',
  },
  body: JSON.stringify({
    informal_statement: 'For every even integer n, 4 divides n^2.',
    generate_informal_proof: true,
    generate_formal_statement: true,
    generate_formal_proof: true,
    max_statement_iters: 3,
    max_proof_iters: 4
  })
});

const result = await response.json();
console.log('Result:', result);
```

## Error Handling

All endpoints follow standard HTTP status codes:

- **200 OK**: Request successful
- **400 Bad Request**: Invalid request parameters
- **422 Unprocessable Entity**: Request validation failed
- **500 Internal Server Error**: Server-side error during processing

Error responses include a `detail` field with a human-readable error message:

```json
{
  "detail": "Error message explaining what went wrong"
}
```

## Rate Limiting

Currently, no rate limiting is implemented. For production deployments, consider adding rate limiting middleware to prevent abuse.

## Interactive Documentation

When the server is running, visit:
- **Swagger UI**: `http://localhost:8000/docs`
- **ReDoc**: `http://localhost:8000/redoc`

These provide interactive API documentation where you can test endpoints directly from your browser.
