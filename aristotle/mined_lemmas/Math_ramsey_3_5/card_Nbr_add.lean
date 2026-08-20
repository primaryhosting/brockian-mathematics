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

lemma card_Nbr_add (c : ℕ → ℕ → Bool) {s : Finset ℕ} {v : ℕ} (hv : v ∈ s) :
    (Nbr c s v true).card + (Nbr c s v false).card = s.card - 1 := by
  have h1 : Nbr c s v false = (s.erase v).filter (fun u => ¬ (c v u = true)) := by
    apply Finset.filter_congr
    intro u _
    simp
  rw [Nbr, h1, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

