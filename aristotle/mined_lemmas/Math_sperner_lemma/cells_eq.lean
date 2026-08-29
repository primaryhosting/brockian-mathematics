import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma cells_eq (J : Finset (Fin (n + 1))) :
    spernerCells (carrier n) (cplx n) J = {J} := by
  ext σ
  simp only [spernerCells, cplx, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, carrier, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hcard, hsub⟩
    exact Finset.eq_of_subset_of_card_le hsub hcard.ge
  · rintro rfl
    exact ⟨rfl, fun v hv => hv⟩

