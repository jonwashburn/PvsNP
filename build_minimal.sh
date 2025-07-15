#!/bin/bash

# Build script that avoids proofwidgets issues
# by building only the essential parts we need

set -e

echo "Starting minimal build..."

# Clean any previous build
rm -rf .lake

# Update dependencies
echo "Updating dependencies..."
lake update

# Build only the core mathlib components we need
echo "Building essential mathlib components..."
lake build Mathlib.Computability.TuringMachine
lake build Mathlib.Data.Nat.Defs
lake build Mathlib.Logic.Function.Basic
lake build Mathlib.Data.Finset.Basic
lake build Mathlib.Data.Fintype.Basic
lake build Mathlib.Data.Real.Basic
lake build Mathlib.Data.Nat.Log

# Build our modules
echo "Building our P vs NP proof modules..."
lake build PvsNP.ClayMinimal.ClassicalEmbed
lake build PvsNP.ClayMinimal.InfoBound
lake build PvsNP.ClayMinimal.ComputationBound
lake build PvsNP.ClayMinimal.ClayMain

echo "Build completed successfully!" 