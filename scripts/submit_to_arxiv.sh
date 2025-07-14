#!/bin/bash

# arXiv Submission Automation Script
# Usage: ./submit_to_arxiv.sh

set -e

echo "🚀 P vs NP arXiv Submission Automation"
echo "======================================"

# Configuration
PAPER_TEX="docs/PvsNP_Academic_Paper.tex"
PAPER_PDF="docs/PvsNP_Academic_Paper.pdf"
TITLE="Scale-Dependent Resolution of P vs NP: A Formal Proof in Lean 4"
AUTHOR="Jonathan Washburn"
CATEGORY="cs.CC"
REPO_URL="https://github.com/jonwashburn/PvsNP"

# Step 1: Check if files exist
echo "📋 Checking submission files..."
if [ ! -f "$PAPER_TEX" ]; then
    echo "❌ Error: $PAPER_TEX not found"
    exit 1
fi

if [ ! -f "$PAPER_PDF" ]; then
    echo "❌ Error: $PAPER_PDF not found"
    echo "📝 Please compile the LaTeX first:"
    echo "   Option 1: Use Overleaf (https://overleaf.com)"
    echo "   Option 2: Run 'pdflatex $PAPER_TEX' if LaTeX is installed"
    exit 1
fi

echo "✅ Files found:"
echo "   - LaTeX source: $PAPER_TEX"
echo "   - PDF: $PAPER_PDF"

# Step 2: Validate PDF
echo "🔍 Validating PDF..."
if command -v pdfinfo >/dev/null 2>&1; then
    PAGE_COUNT=$(pdfinfo "$PAPER_PDF" | grep "Pages:" | awk '{print $2}')
    echo "   PDF has $PAGE_COUNT pages"
else
    echo "   PDF validation skipped (pdfinfo not available)"
fi

# Step 3: Extract abstract from LaTeX
echo "📖 Extracting abstract..."
ABSTRACT=$(grep -A 20 '\\begin{abstract}' "$PAPER_TEX" | grep -B 20 '\\end{abstract}' | head -n -1 | tail -n +2 | tr '\n' ' ' | sed 's/  */ /g')
echo "   Abstract length: ${#ABSTRACT} characters"

# Step 4: Generate submission summary
echo "📋 Generating submission summary..."
cat > docs/arxiv_submission_summary.txt << EOF
arXiv Submission Summary
========================

Title: $TITLE
Author: $AUTHOR
Category: $CATEGORY (Computational Complexity)
Secondary: cs.LO (Logic in Computer Science) - optional

Abstract:
$ABSTRACT

Comments for arXiv:
Formal proof in Lean 4 with zero sorries. Repository: $REPO_URL

MSC Class: 68Q15 (Complexity classes)

Files to upload:
- Main file: $PAPER_TEX
- PDF file: $PAPER_PDF

Submission URL: https://arxiv.org/submit

Post-submission actions:
1. Share on Lean Zulip (#general)
2. Post on Reddit r/lean
3. Engage TCS Stack Exchange
4. Contact complexity theorists
5. Monitor reception and feedback

Repository: $REPO_URL
Date: $(date)
EOF

echo "✅ Submission summary created: docs/arxiv_submission_summary.txt"

# Step 5: Open required URLs
echo "🌐 Opening submission resources..."
if command -v open >/dev/null 2>&1; then
    open "https://arxiv.org/submit"
    sleep 2
    open "$REPO_URL"
else
    echo "   Please visit: https://arxiv.org/submit"
    echo "   Repository: $REPO_URL"
fi

# Step 6: Display next steps
echo ""
echo "🎯 NEXT STEPS:"
echo "==============="
echo "1. 📤 Upload to arXiv:"
echo "   - Go to https://arxiv.org/submit"
echo "   - Upload $PAPER_TEX as main file"
echo "   - Upload $PAPER_PDF as PDF"
echo "   - Use details from: docs/arxiv_submission_summary.txt"
echo ""
echo "2. 🔄 Once published, update templates:"
echo "   - Replace '[link when available]' with arXiv URL"
echo "   - Use templates from: docs/Community_Engagement_Templates.md"
echo ""
echo "3. 📢 Community engagement (Day 1-2):"
echo "   - Lean Zulip: https://leanprover.zulipchat.com/"
echo "   - Reddit r/lean: https://reddit.com/r/lean"
echo ""
echo "4. 📊 Monitor and track:"
echo "   - arXiv download count"
echo "   - GitHub stars/forks"
echo "   - Community feedback"
echo ""
echo "✨ Good luck with your submission!" 