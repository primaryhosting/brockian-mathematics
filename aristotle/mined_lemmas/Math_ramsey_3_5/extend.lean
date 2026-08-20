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

lemma extend {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s t : Finset ℕ} {v : ℕ}
    {b : Bool} (hv : v ∈ s) (hts : t ⊆ Nbr c s v b) (ht : Mono c b t) :
    ∃ t' ⊆ s, t'.card = t.card + 1 ∧ Mono c b t' := by
  have hvt : v ∉ t := by
    intro hvt
    exact ((mem_Nbr.mp (hts hvt)).1.2) rfl
  refine ⟨insert v t, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact (mem_Nbr.mp (hts hx)).1.1
  · exact Finset.card_insert_of_notMem hvt
  · intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact (mem_Nbr.mp (hts hy)).2
    · rcases hy with rfl | hy
      · rw [hsym]
        exact (mem_Nbr.mp (hts hx)).2
      · exact ht x hx y hy hxy

/-- `R(2, q) ≤ q`. -/
