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

theorem sum_nbhd_eq (T : Finset V) :
    ∑ v ∈ T, (nbhd G T v).card = ((T ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp only [nbhd_eq_filter, Finset.card_filter]

/-- Handshake parity: the number of ordered adjacent pairs inside `T` is even. -/
