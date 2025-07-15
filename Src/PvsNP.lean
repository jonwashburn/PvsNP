/-
  PvsNP - P vs NP Project Root File

  This is the main entry point for the PvsNP project. Lake builds this file,
  which imports all the main modules to ensure the entire project compiles.

  The project aims to formalize aspects of the P vs NP problem using
  Recognition Science theory and information-theoretic bounds.
-/

-- Core definitions and helpers
import PvsNP.Helpers.VerificationComplexity

-- Fundamental complexity theory
import PvsNP.ComplexityClassesEnhanced
import PvsNP.ComplexityGlue
import PvsNP.AsymptoticAnalysis

-- Recognition Science framework
import PvsNP.RSFoundation
import PvsNP.ScaleSeparation
import PvsNP.RecognitionBound
import PvsNP.LedgerWorld
import PvsNP.InterfacePoints

-- Main theorems and proofs
import PvsNP.MainTheorem
import PvsNP.MainTheoremA0

-- Classical computation models
import PvsNP.TuringMachine
import PvsNP.CellularAutomaton
import PvsNP.BalancedParity

-- Bridge between classical and recognition approaches
import PvsNP.ClassicalBridge
import PvsNP.ClayInstituteProof

-- Clay Institute minimal framework
import PvsNP.ClayMinimal.ComputationBound
import PvsNP.ClayMinimal.InfoBound
import PvsNP.ClayMinimal.ClassicalEmbed
import PvsNP.ClayMinimal.ClayMain

-- Enhanced consciousness and gap analysis
import PvsNP.ConsciousnessEnhancement
import PvsNP.Gap45Consciousness
import PvsNP.Gap45Enhancement
import PvsNP.DeepestTruth

-- Meta-theoretical foundations
import PvsNP.MetaAxiom
import PvsNP.NoEliminator
import PvsNP.ExperimentalMathFoundation

-- Test cases and examples
import PvsNP.Example

/-!
## Project Overview

This project formalizes a proposed solution to the P vs NP problem using:

1. **Recognition Science**: A parameter-free framework based on eight axioms
   and golden ratio constraints for measuring computational complexity.

2. **Information-theoretic bounds**: Lower bounds on recognition vs computation
   complexity using octave analysis and entropy arguments.

3. **Cellular automaton computation**: Upper bounds showing SAT solvable
   in O(n^{1/3}) time using reversible 3D cellular automata.

4. **Classical bridge**: Connection between Turing machine complexity and
   recognition science measurements.

## Build Status

All modules should compile without `sorry`, `admit`, or undefined references.
Run `lake build` to verify the entire project compiles successfully.

If there are compilation errors, they indicate missing definitions or
proof gaps that need to be addressed.

Note: Some files reference missing modules (like SATEncoding) and may need
to be updated to use existing SAT functionality from ClayMinimal.ClassicalEmbed.
-/

namespace PvsNP

-- Re-export key definitions for convenient access
open ComplexityClassesEnhanced (NP_recognition NP_measurement)
open Helpers.VerificationComplexity (verification_complexity)

end PvsNP
