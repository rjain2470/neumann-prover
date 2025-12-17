# Vercel Deployment Guide for Neumann Prover

This guide explains how to deploy the Neumann Prover web interface to Vercel, making it accessible via a public URL.

## Prerequisites

1. A Vercel account (free) - sign up at https://vercel.com
2. Vercel CLI installed (optional, for command-line deployment)
3. Your API keys for OpenAI, Anthropic, and/or Together AI

## Deployment Methods

### Method 1: GitHub Integration (Recommended)

This is the easiest method and enables automatic deployments on every push.

1. **Connect Repository to Vercel**
   - Go to https://vercel.com/new
   - Click "Import Git Repository"
   - Select your `neumann-prover` repository
   - Vercel will auto-detect the configuration from `vercel.json`

2. **Configure Environment Variables**
   - In the Vercel project settings, go to "Environment Variables"
   - Add the following variables:
     - `OPENAI_API_KEY` = your OpenAI API key
     - `ANTHROPIC_API_KEY` = your Anthropic API key
     - `TOGETHER_API_KEY` = your Together AI API key
   - Make sure to set them for "Production", "Preview", and "Development" environments

3. **Deploy**
   - Click "Deploy"
   - Wait for the build to complete (~2-5 minutes)
   - Your app will be available at: `https://neumannprover.vercel.app` (or similar)

### Method 2: Vercel CLI

If you prefer command-line deployment:

1. **Install Vercel CLI**
   ```bash
   npm install -g vercel
   ```

2. **Login to Vercel**
   ```bash
   vercel login
   ```

3. **Deploy from Repository Root**
   ```bash
   cd /path/to/neumann-prover
   vercel
   ```

4. **Follow the prompts**
   - Link to existing project or create new one
   - Set project name (e.g., "neumannprover")
   - Confirm build settings

5. **Set Environment Variables**
   ```bash
   vercel env add OPENAI_API_KEY
   vercel env add ANTHROPIC_API_KEY
   vercel env add TOGETHER_API_KEY
   ```

6. **Deploy to Production**
   ```bash
   vercel --prod
   ```

## Your Deployment URL

After successful deployment, your web interface will be accessible at:
- **Vercel Subdomain**: `https://neumannprover.vercel.app`
- **Custom Domain** (optional): Configure in Vercel project settings

## Post-Deployment

### Accessing Your App
Simply visit your Vercel URL in any browser. Users can:
1. Enter their API keys (stored locally in browser)
2. Input mathematical statements
3. Generate formal proofs
4. View and export results

### Automatic Deployments
Once connected via GitHub, every push to your main branch triggers:
- Automatic rebuild
- Automatic deployment
- Zero downtime updates

### Monitoring
- View deployment logs in Vercel dashboard
- Monitor API usage and errors
- Check real-time analytics

## Vercel Configuration Files

The following files configure Vercel deployment:

### `vercel.json`
Main configuration file that tells Vercel how to build and route your app.

### `requirements.txt`
Python dependencies that Vercel installs during build.

### `api/index.py`
Entry point that adapts the FastAPI app for Vercel's serverless functions.

## Important Notes

### Lean Compilation Limitations
⚠️ **Note**: Vercel's serverless functions have limitations that may affect Lean compilation:
- **Execution time limit**: 10 seconds (Hobby), 60 seconds (Pro)
- **Memory limit**: 1 GB (Hobby), 3 GB (Pro)
- **No persistent filesystem**: Lean projects are ephemeral

For full Lean compilation support, consider:
- Using the `/api/generate` endpoint for proof generation (without Lean compilation)
- Deploying to a service with persistent storage (Railway, Render, Fly.io)
- Running Lean compilation locally

### API Key Security
API keys are:
- Stored client-side in browser localStorage
- Sent as environment variables to Vercel (secure)
- Never exposed in logs or client-side code

## Troubleshooting

### Build Fails
- Check that `requirements.txt` includes all dependencies
- Verify Python version compatibility (Vercel uses Python 3.9+)
- Review build logs in Vercel dashboard

### Environment Variables Not Working
- Ensure variables are set for the correct environment (Production/Preview/Development)
- Redeploy after adding new environment variables
- Check variable names match exactly (case-sensitive)

### Static Files Not Loading
- Verify the static files are in `src/neumann_prover/static/`
- Check that the app mounts static files correctly
- Review browser console for 404 errors

### API Endpoints Return 404
- Ensure `vercel.json` routes are configured correctly
- Check that `api/index.py` imports the FastAPI app properly
- Verify the app is running by checking `/api/health` endpoint

## Upgrading to Custom Domain

Once deployed, you can add a custom domain:

1. **Purchase a Domain**
   - Buy from Namecheap, GoDaddy, or any registrar
   - Recommended: `neumannprover.com` or `neumannprover.ai`

2. **Add to Vercel**
   - Go to your project settings in Vercel
   - Navigate to "Domains"
   - Add your custom domain
   - Follow DNS configuration instructions

3. **Update DNS**
   - Add the CNAME or A records provided by Vercel
   - Wait for DNS propagation (up to 48 hours, usually faster)

4. **SSL Certificate**
   - Vercel automatically provisions SSL certificates
   - Your site will be accessible via HTTPS

## Support

For issues with:
- **Vercel deployment**: Check https://vercel.com/docs
- **Neumann Prover code**: Open an issue on GitHub
- **API integrations**: Refer to provider documentation (OpenAI, Anthropic, Together)

## Example: Sharing Your Deployment

Once deployed, you can share the URL with anyone:

```
Visit: https://neumannprover.vercel.app

Users can:
1. Enter their own API keys (or use server-side keys if configured)
2. Input informal mathematical statements
3. Generate formal Lean proofs
4. Download results
```

No installation required - just a web browser!
