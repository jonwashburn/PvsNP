#!/bin/bash
#
# This script compiles the LaTeX paper, including the bibliography.
# It uses 'latexmk', which automates the multi-step compile process.
#
# To run:
# 1. Make sure you have a TeX distribution installed (like MacTeX, TeX Live).
# 2. Open a terminal in this directory.
# 3. Run the command: sh build.sh

FILENAME="P-vs-NP-Complete_Theory_of_Physical_Computation.txt"

# Check if latexmk is installed
if ! command -v latexmk &> /dev/null
then
    echo "Error: 'latexmk' is not installed. Please install a TeX distribution."
    exit 1
fi

echo "Compiling $FILENAME with latexmk..."

# Run latexmk to handle all compilation steps automatically
# -pdf: generate a PDF
# -bibtex: run bibtex if needed
latexmk -pdf -bibtex "$FILENAME"

echo ""
echo "Compilation complete."
echo "Output file: ${FILENAME%.*}.pdf" 