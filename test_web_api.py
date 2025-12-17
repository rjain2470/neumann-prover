"""
Simple test to verify web API functionality
"""
import pytest
from starlette.testclient import TestClient
from neumann_prover.web_app import app


@pytest.fixture
def client():
    """Test client fixture"""
    return TestClient(app)


def test_root_endpoint(client):
    """Test that root endpoint returns HTML"""
    response = client.get("/")
    assert response.status_code == 200
    assert "Neumann Prover" in response.text


def test_stages_endpoint(client):
    """Test that stages endpoint returns valid data"""
    response = client.get("/api/stages")
    assert response.status_code == 200
    
    data = response.json()
    assert "stages" in data
    assert "stage_list" in data
    assert isinstance(data["stages"], dict)
    assert isinstance(data["stage_list"], list)
    
    # Check that some expected stages exist
    assert "informal_proof" in data["stages"]
    assert "formal_statement_draft" in data["stages"]
    assert "formal_proof_draft" in data["stages"]


def test_models_endpoint(client):
    """Test that models endpoint returns valid data"""
    response = client.get("/api/models")
    assert response.status_code == 200
    
    data = response.json()
    assert "models" in data
    assert "all_models" in data
    assert isinstance(data["models"], dict)
    assert isinstance(data["all_models"], list)
    
    # Check that providers exist
    assert "openai" in data["models"]
    assert "anthropic" in data["models"]
    assert "together" in data["models"]


def test_health_endpoint(client):
    """Test that health endpoint returns status"""
    response = client.get("/api/health")
    assert response.status_code == 200
    
    data = response.json()
    assert "status" in data
    assert data["status"] == "healthy"
    assert "lean_available" in data
    assert "environment_vars" in data


def test_compile_endpoint_basic(client):
    """Test compile endpoint with simple code"""
    response = client.post("/api/compile", json={
        "lean_code": "import Mathlib\n\ntheorem test : True := trivial",
        "filename": "Test.lean"
    })
    assert response.status_code == 200
    
    data = response.json()
    assert "success" in data
    assert "code" in data
    assert "import Mathlib" in data["code"]


def test_generate_endpoint_validation(client):
    """Test that generate endpoint validates required fields"""
    # Missing informal_statement should fail validation
    response = client.post("/api/generate", json={})
    assert response.status_code == 422  # Unprocessable Entity


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
