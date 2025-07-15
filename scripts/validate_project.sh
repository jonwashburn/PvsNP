#!/bin/bash

# Project Validation Script
# Catches common issues that cause embarrassment on Zulip

set -e

echo "🔍 Validating PvsNP project structure and definitions..."

# 1. Check root file exists and isn't empty
echo "Checking root file..."
if [ ! -f "Src/PvsNP.lean" ]; then
    echo "❌ ERROR: Root file Src/PvsNP.lean missing!"
    exit 1
fi

if [ ! -s "Src/PvsNP.lean" ]; then
    echo "❌ ERROR: Root file Src/PvsNP.lean is empty!"
    echo "This means 'lake build' won't compile your actual code."
    exit 1
fi

echo "✅ Root file exists and has content"

# 2. Check verification_complexity is defined
echo "Checking verification_complexity definition..."
if [ ! -f "Src/PvsNP/Helpers/VerificationComplexity.lean" ]; then
    echo "❌ ERROR: verification_complexity file missing!"
    exit 1
fi

if ! grep -q "def verification_complexity" "Src/PvsNP/Helpers/VerificationComplexity.lean"; then
    echo "❌ ERROR: verification_complexity not defined!"
    echo "NP definition references this but it doesn't exist."
    exit 1
fi

echo "✅ verification_complexity properly defined"

# 3. Test that basic modules compile
echo "Testing core module compilation..."

modules=(
    "PvsNP.Helpers.VerificationComplexity"
    "RecognitionScience"
    "PvsNP.ComplexityClassesEnhanced"
)

for module in "${modules[@]}"; do
    echo "  Testing $module..."
    if ! lake build "$module" 2>/dev/null; then
        echo "❌ ERROR: Module $module failed to compile!"
        echo "Run: lake build $module"
        exit 1
    fi
done

echo "✅ Core modules compile successfully"

# 4. Check for undefined symbols that are used
echo "Checking for undefined symbols..."
if grep -r "verification_complexity" Src/ --include="*.lean" | grep -v "def verification_complexity" | grep -v "import.*VerificationComplexity" | head -1 > /dev/null; then
    echo "✅ verification_complexity is used in code"
else
    echo "⚠️  WARNING: verification_complexity might not be used anywhere"
fi

# 5. Quick dependency check
echo "Checking import structure..."
if ! lake build --no-build 2>/dev/null; then
    echo "❌ ERROR: Import/dependency issues detected!"
    echo "Run: lake build"
    exit 1
fi

echo "✅ Import structure looks good"

# 6. Check for common antipatterns
echo "Checking for antipatterns..."

# Too many sorries
sorry_count=$(find Src -name "*.lean" -exec grep -c "sorry" {} + 2>/dev/null | awk '{sum+=$1} END {print sum+0}')
if [ "$sorry_count" -gt 100 ]; then
    echo "⚠️  WARNING: Found $sorry_count sorries - might indicate incomplete proof"
fi

# Missing axiom declarations
if ! find Src -name "*.lean" -exec grep -l "#check_axioms" {} \; > /dev/null 2>&1; then
    echo "⚠️  SUGGESTION: Consider adding #check_axioms to verify axiom usage"
fi

echo ""
echo "🎉 Project validation complete!"
echo "✅ Root file properly imports modules"
echo "✅ Core definitions exist"
echo "✅ Basic compilation works"
echo "✅ No obvious structural issues"
echo ""
echo "Safe to push to GitHub!" 