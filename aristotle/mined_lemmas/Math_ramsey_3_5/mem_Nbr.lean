import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma mem_Nbr {c : ℕ → ℕ → Bool} {s : Finset ℕ} {v u : ℕ} {b : Bool} :
    u ∈ Nbr c s v b ↔ (u ∈ s ∧ u ≠ v) ∧ c v u = b := by
  simp [Nbr, Finset.mem_filter, Finset.mem_erase, and_comm]

