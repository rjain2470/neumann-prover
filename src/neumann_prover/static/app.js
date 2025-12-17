/**
 * Neumann Prover Web Interface - Main JavaScript
 */

// API Base URL - adjust for production
const API_BASE = window.location.origin;

// Storage keys
const STORAGE_KEYS = {
    OPENAI_KEY: 'neumann_openai_key',
    ANTHROPIC_KEY: 'neumann_anthropic_key',
    TOGETHER_KEY: 'neumann_together_key',
};

// Global state
let stagesData = null;
let modelsData = null;
let currentResults = null;

/**
 * Initialize the application
 */
document.addEventListener('DOMContentLoaded', async () => {
    // Load saved API keys
    loadApiKeys();
    
    // Load stages and models from API
    await loadStagesAndModels();
    
    // Initialize syntax highlighting
    if (typeof hljs !== 'undefined') {
        hljs.highlightAll();
    }
    
    console.log('Neumann Prover Web Interface initialized');
});

/**
 * Load API keys from localStorage
 */
function loadApiKeys() {
    const openaiKey = localStorage.getItem(STORAGE_KEYS.OPENAI_KEY);
    const anthropicKey = localStorage.getItem(STORAGE_KEYS.ANTHROPIC_KEY);
    const togetherKey = localStorage.getItem(STORAGE_KEYS.TOGETHER_KEY);
    
    if (openaiKey) {
        document.getElementById('openai-key').value = openaiKey;
        updateKeyStatus('openai', true);
    }
    if (anthropicKey) {
        document.getElementById('anthropic-key').value = anthropicKey;
        updateKeyStatus('anthropic', true);
    }
    if (togetherKey) {
        document.getElementById('together-key').value = togetherKey;
        updateKeyStatus('together', true);
    }
}

/**
 * Save API keys to localStorage
 */
function saveApiKeys() {
    const openaiKey = document.getElementById('openai-key').value.trim();
    const anthropicKey = document.getElementById('anthropic-key').value.trim();
    const togetherKey = document.getElementById('together-key').value.trim();
    
    if (openaiKey) {
        localStorage.setItem(STORAGE_KEYS.OPENAI_KEY, openaiKey);
        updateKeyStatus('openai', true);
    }
    if (anthropicKey) {
        localStorage.setItem(STORAGE_KEYS.ANTHROPIC_KEY, anthropicKey);
        updateKeyStatus('anthropic', true);
    }
    if (togetherKey) {
        localStorage.setItem(STORAGE_KEYS.TOGETHER_KEY, togetherKey);
        updateKeyStatus('together', true);
    }
    
    alert('API keys saved securely in your browser!');
}

/**
 * Update key status indicator
 */
function updateKeyStatus(provider, connected) {
    const statusEl = document.getElementById(`${provider}-status`);
    if (statusEl) {
        statusEl.className = `status-indicator ${connected ? 'connected' : 'disconnected'}`;
    }
}

/**
 * Load stages and models from API
 */
async function loadStagesAndModels() {
    try {
        // Load stages
        const stagesResponse = await fetch(`${API_BASE}/api/stages`);
        stagesData = await stagesResponse.json();
        
        // Load models
        const modelsResponse = await fetch(`${API_BASE}/api/models`);
        modelsData = await modelsResponse.json();
        
        // Populate model dropdowns
        populateModelSelects();
        
        // Show default models
        updateDefaultModelLabels();
        
    } catch (error) {
        console.error('Error loading stages and models:', error);
        alert('Warning: Could not load model configurations from server. Using defaults.');
    }
}

/**
 * Populate model selection dropdowns
 */
function populateModelSelects() {
    if (!modelsData) return;
    
    const selects = ['model-informal', 'model-statement', 'model-proof'];
    
    selects.forEach(selectId => {
        const select = document.getElementById(selectId);
        if (!select) return;
        
        // Clear existing options except default
        while (select.options.length > 1) {
            select.remove(1);
        }
        
        // Add optgroups for each provider
        Object.entries(modelsData.models).forEach(([provider, models]) => {
            const optgroup = document.createElement('optgroup');
            optgroup.label = provider.charAt(0).toUpperCase() + provider.slice(1);
            
            models.forEach(model => {
                const option = document.createElement('option');
                option.value = model;
                option.textContent = model;
                optgroup.appendChild(option);
            });
            
            select.appendChild(optgroup);
        });
    });
}

/**
 * Update default model labels
 */
function updateDefaultModelLabels() {
    if (!stagesData) return;
    
    const mappings = {
        'informal_proof': 'default-informal',
        'formal_statement_draft': 'default-statement',
        'formal_proof_draft': 'default-proof',
    };
    
    Object.entries(mappings).forEach(([stage, elementId]) => {
        const defaultModel = stagesData.stages[stage];
        const element = document.getElementById(elementId);
        if (element && defaultModel) {
            element.textContent = `Default: ${defaultModel}`;
        }
    });
}

/**
 * Toggle input sections based on checkboxes
 */
function toggleInput(sectionId) {
    const section = document.getElementById(sectionId);
    const checkbox = document.getElementById(`input-${sectionId.replace('-section', '')}`);
    
    if (section && checkbox) {
        section.classList.toggle('hidden', !checkbox.checked);
    }
}

/**
 * Main generate proof function
 */
async function generateProof() {
    // Validate inputs
    const informalStatement = document.getElementById('informal-statement').value.trim();
    if (!informalStatement) {
        alert('Please enter an informal mathematical statement.');
        return;
    }
    
    // Check if at least one API key is available
    const hasApiKey = localStorage.getItem(STORAGE_KEYS.OPENAI_KEY) ||
                      localStorage.getItem(STORAGE_KEYS.ANTHROPIC_KEY) ||
                      localStorage.getItem(STORAGE_KEYS.TOGETHER_KEY);
    
    if (!hasApiKey) {
        alert('Please configure at least one API key before generating proofs.');
        return;
    }
    
    // Prepare request data
    const requestData = {
        informal_statement: informalStatement,
        informal_proof: getOptionalInput('informal-proof'),
        formal_statement: getOptionalInput('formal-statement'),
        lean_pseudocode: getOptionalInput('pseudocode'),
        previous_errors: getOptionalInput('prev-errors'),
        
        generate_informal_proof: document.getElementById('output-informal-proof').checked,
        generate_formal_statement: document.getElementById('output-formal-statement').checked,
        generate_formal_proof: document.getElementById('output-formal-proof').checked,
        generate_pseudocode: document.getElementById('output-pseudocode').checked,
        
        model_informal: getModelSelection('model-informal'),
        model_statement: getModelSelection('model-statement'),
        model_proof: getModelSelection('model-proof'),
        
        temperature: parseFloat(document.getElementById('temperature').value),
        max_statement_iters: parseInt(document.getElementById('max-statement-iters').value),
        max_proof_iters: parseInt(document.getElementById('max-proof-iters').value),
        project_root: document.getElementById('project-root').value.trim() || null,
    };
    
    // Set API keys as headers (they'll be used by the backend)
    const headers = {
        'Content-Type': 'application/json',
    };
    
    // Note: In a real production setup, you'd send these keys securely
    // For now, we're relying on environment variables on the server side
    
    // Show progress
    showProgress();
    disableGenerateButton();
    
    try {
        const response = await fetch(`${API_BASE}/api/generate`, {
            method: 'POST',
            headers: headers,
            body: JSON.stringify(requestData),
        });
        
        if (!response.ok) {
            const error = await response.json();
            throw new Error(error.detail || 'Generation failed');
        }
        
        const results = await response.json();
        currentResults = results;
        
        // Hide progress and show results
        hideProgress();
        displayResults(results);
        
    } catch (error) {
        console.error('Generation error:', error);
        alert(`Error: ${error.message}`);
        hideProgress();
    } finally {
        enableGenerateButton();
    }
}

/**
 * Get optional input value
 */
function getOptionalInput(inputId) {
    const checkbox = document.getElementById(`input-${inputId}`);
    if (checkbox && checkbox.checked) {
        const value = document.getElementById(inputId).value.trim();
        return value || null;
    }
    return null;
}

/**
 * Get model selection
 */
function getModelSelection(selectId) {
    const value = document.getElementById(selectId).value;
    return value || null;
}

/**
 * Show progress bar
 */
function showProgress() {
    const progressSection = document.getElementById('progress-section');
    progressSection.classList.remove('hidden');
    
    // Simulate progress animation
    const progressFill = document.getElementById('progress-fill');
    const progressText = document.getElementById('progress-text');
    
    let progress = 0;
    const interval = setInterval(() => {
        progress += Math.random() * 10;
        if (progress > 90) progress = 90; // Cap at 90% until completion
        
        progressFill.style.width = `${progress}%`;
        
        // Update text based on progress
        if (progress < 30) {
            progressText.textContent = 'Generating informal proof...';
        } else if (progress < 60) {
            progressText.textContent = 'Generating formal statement...';
        } else {
            progressText.textContent = 'Generating formal proof...';
        }
    }, 500);
    
    // Store interval ID for later cleanup
    progressSection.dataset.intervalId = interval;
}

/**
 * Hide progress bar
 */
function hideProgress() {
    const progressSection = document.getElementById('progress-section');
    const progressFill = document.getElementById('progress-fill');
    const progressText = document.getElementById('progress-text');
    
    // Clear interval
    const intervalId = progressSection.dataset.intervalId;
    if (intervalId) {
        clearInterval(parseInt(intervalId));
    }
    
    // Complete the progress bar
    progressFill.style.width = '100%';
    progressText.textContent = 'Complete!';
    
    // Hide after a short delay
    setTimeout(() => {
        progressSection.classList.add('hidden');
        progressFill.style.width = '0%';
    }, 1000);
}

/**
 * Disable generate button
 */
function disableGenerateButton() {
    const btn = document.getElementById('generate-btn');
    btn.disabled = true;
    btn.innerHTML = '<span class="spinner"></span> Generating...';
}

/**
 * Enable generate button
 */
function enableGenerateButton() {
    const btn = document.getElementById('generate-btn');
    btn.disabled = false;
    btn.innerHTML = '🚀 Generate Proof';
}

/**
 * Display results
 */
function displayResults(results) {
    const resultsSection = document.getElementById('results-section');
    const resultsContainer = document.getElementById('results-container');
    
    resultsSection.classList.remove('hidden');
    resultsContainer.innerHTML = '';
    
    // Display summary
    if (results.summary) {
        const summaryCard = createSummaryCard(results.summary);
        resultsContainer.appendChild(summaryCard);
    }
    
    // Display informal proof
    if (results.informal_proof) {
        const card = createResultCard(
            'Informal Proof',
            results.informal_proof.text,
            'text',
            true
        );
        resultsContainer.appendChild(card);
    }
    
    // Display pseudocode
    if (results.pseudocode) {
        const card = createResultCard(
            'Lean Pseudocode',
            results.pseudocode.text,
            'code',
            true
        );
        resultsContainer.appendChild(card);
    }
    
    // Display formal statement
    if (results.formal_statement) {
        const card = createResultCard(
            'Formal Statement',
            results.formal_statement.text,
            'lean',
            results.formal_statement.compiled,
            results.formal_statement.stderr || results.formal_statement.stdout
        );
        resultsContainer.appendChild(card);
    }
    
    // Display formal proof
    if (results.formal_proof) {
        const card = createResultCard(
            'Formal Proof',
            results.formal_proof.text,
            'lean',
            results.formal_proof.compiled,
            results.formal_proof.stderr || results.formal_proof.stdout
        );
        resultsContainer.appendChild(card);
    }
    
    // Scroll to results
    resultsSection.scrollIntoView({ behavior: 'smooth', block: 'start' });
}

/**
 * Create summary card
 */
function createSummaryCard(summary) {
    const card = document.createElement('div');
    card.className = 'result-card';
    
    const html = `
        <div class="result-header">
            <div class="result-title">📊 Generation Summary</div>
        </div>
        <div class="result-content">
            <p><strong>Items Processed:</strong> ${summary.n_items || 1}</p>
            <p><strong>Formal Statements Compiled:</strong> ${summary.statements_compiled || 0} ✅</p>
            <p><strong>Formal Proofs Compiled:</strong> ${summary.proofs_compiled || 0} ✅</p>
            <p><strong>Time Elapsed:</strong> ${summary.elapsed_sec || 0}s</p>
        </div>
    `;
    
    card.innerHTML = html;
    return card;
}

/**
 * Create result card
 */
function createResultCard(title, content, language, compiled = null, error = null) {
    const card = document.createElement('div');
    card.className = 'result-card';
    
    let statusBadge = '';
    if (compiled !== null) {
        if (compiled) {
            statusBadge = '<span class="status-badge success">✅ Compiles</span>';
        } else {
            statusBadge = '<span class="status-badge error">❌ Errors</span>';
        }
    }
    
    const errorHtml = error ? `
        <div class="error-details">
            <strong>Compiler Output:</strong><br>
            ${escapeHtml(error)}
        </div>
    ` : '';
    
    const contentHtml = language === 'text' 
        ? `<p>${escapeHtml(content)}</p>`
        : `<pre><code class="language-${language}">${escapeHtml(content)}</code></pre>`;
    
    const html = `
        <div class="result-header" onclick="toggleResultContent(this)">
            <div class="result-title">${title}</div>
            ${statusBadge}
        </div>
        <div class="result-content expandable-content expanded">
            ${contentHtml}
            ${errorHtml}
        </div>
    `;
    
    card.innerHTML = html;
    
    // Apply syntax highlighting if available
    setTimeout(() => {
        if (typeof hljs !== 'undefined') {
            card.querySelectorAll('pre code').forEach(block => {
                hljs.highlightElement(block);
            });
        }
    }, 0);
    
    return card;
}

/**
 * Toggle result content visibility
 */
function toggleResultContent(headerEl) {
    const content = headerEl.nextElementSibling;
    content.classList.toggle('expanded');
}

/**
 * Escape HTML
 */
function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

/**
 * Export results
 */
function exportResults() {
    if (!currentResults) {
        alert('No results to export');
        return;
    }
    
    // Create export data
    const exportData = {
        timestamp: new Date().toISOString(),
        results: currentResults,
    };
    
    // Create downloadable file
    const blob = new Blob([JSON.stringify(exportData, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `neumann-prover-results-${Date.now()}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
    
    alert('Results exported successfully!');
}

/**
 * Reset form
 */
function resetForm() {
    if (confirm('Are you sure you want to reset the form? This will clear all inputs and results.')) {
        // Clear input fields
        document.getElementById('informal-statement').value = '';
        document.getElementById('informal-proof').value = '';
        document.getElementById('formal-statement').value = '';
        document.getElementById('pseudocode').value = '';
        document.getElementById('prev-errors').value = '';
        
        // Reset checkboxes
        document.getElementById('input-informal-proof').checked = false;
        document.getElementById('input-formal-statement').checked = false;
        document.getElementById('input-pseudocode').checked = false;
        document.getElementById('input-prev-errors').checked = false;
        
        // Hide optional sections
        document.getElementById('informal-proof-section').classList.add('hidden');
        document.getElementById('formal-statement-section').classList.add('hidden');
        document.getElementById('pseudocode-section').classList.add('hidden');
        document.getElementById('prev-errors-section').classList.add('hidden');
        
        // Reset model selections
        document.getElementById('model-informal').value = '';
        document.getElementById('model-statement').value = '';
        document.getElementById('model-proof').value = '';
        
        // Reset advanced settings
        document.getElementById('temperature').value = '0.7';
        document.getElementById('temp-value').textContent = '0.7';
        document.getElementById('max-statement-iters').value = '3';
        document.getElementById('max-proof-iters').value = '4';
        document.getElementById('project-root').value = '';
        
        // Hide results
        document.getElementById('results-section').classList.add('hidden');
        currentResults = null;
        
        // Scroll to top
        window.scrollTo({ top: 0, behavior: 'smooth' });
    }
}
