/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem card_nbhd_add_card_nonNbhd {T : Finset V} {v : V} (hv : v ∈ T) :
    (nbhd G T v).card + (nonNbhd G T v).card = T.card - 1 := by
  rw [nbhd, nonNbhd, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

