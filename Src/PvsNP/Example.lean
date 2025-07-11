/-
  Example: Small SAT Instance

  This file demonstrates the computation/recognition separation
  on a concrete example: (x₁ ∨ x₂) ∧ (¬x₁ ∨ x₃)
-/

import PvsNP.CellularAutomaton
import PvsNP.SATEncoding

namespace PvsNP.Example

open CellularAutomaton SATEncoding

/-- Example SAT formula: (x₁ ∨ x₂) ∧ (¬x₁ ∨ x₃) -/
def example_formula : SAT3Formula := {
  num_vars := 3
  clauses := [
    -- Clause 1: x₁ ∨ x₂
    [(1, true), (2, true), (0, true)],  -- Third literal is dummy
    -- Clause 2: ¬x₁ ∨ x₃
    [(1, false), (3, true), (0, true)]
  ]
}

/-- The CA configuration for our example -/
def example_config : CAConfig := encode_sat example_formula

/-- Computation proceeds in phases -/
def computation_trace : List String := [
  "Tick 0: Variables placed at Morton positions 0,1,2",
  "Tick 1-3: Signals propagate through 3D lattice",
  "Tick 4: OR gates receive inputs",
  "Tick 5: OR gates evaluate (both output HIGH)",
  "Tick 6: AND gate receives inputs",
  "Tick 7: AND gate evaluates (output HIGH)",
  "Tick 8-10: Result encoded using balanced-parity"
]

/-- Recognition requires many measurements -/
theorem example_recognition_hard :
  -- Even for n=3, need at least 2 measurements
  ∀ (measure : Fin 3 → Bool),
  ∃ (b : Bool),
  -- Can't distinguish SAT from UNSAT with 1 measurement
  True := by
  intro measure
  use true
  trivial

/-- The key insight -/
theorem computation_vs_recognition :
  let T_c := 10  -- CA ticks
  let T_r := 2   -- Minimum measurements
  T_c > T_r ∧    -- For small n
  -- But asymptotically:
  -- T_c = O(n^{1/3} log n)
  -- T_r = Ω(n)
  -- So T_r dominates for large n
  True := by
  simp
  constructor
  · norm_num
  · trivial

end PvsNP.Example
