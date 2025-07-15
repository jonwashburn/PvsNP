/-
  SAT Encoding Module

  This module provides SAT encoding functionality by re-exporting definitions
  from the ClayMinimal.ClassicalEmbed module. This is a compatibility layer
  for files that expect a standalone SATEncoding module.
-/

import PvsNP.ClayMinimal.ClassicalEmbed
import PvsNP.CellularAutomaton

namespace PvsNP.SATEncoding

-- Re-export SAT instance from ClassicalEmbed
open ClayMinimal (SATInstance satisfies)

-- Alias for compatibility
def SAT3Formula := SATInstance

-- Re-export encoding functions
open ClayMinimal (encode_sat_instance decode_sat_instance)

-- Create aliases for expected functions
def encode_sat (formula : SAT3Formula) : List Bool := encode_sat_instance formula
def decode_sat (bits : List Bool) : SAT3Formula := decode_sat_instance bits

-- Cellular automaton integration
open CellularAutomaton

-- Placeholder for CA run function (simplified version)
def ca_run (config : Position3D → CAState) (steps : ℕ) : Position3D → CAState :=
  fun pos => config pos  -- Simplified: just return original config

end PvsNP.SATEncoding
