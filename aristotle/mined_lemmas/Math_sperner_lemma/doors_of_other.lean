/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/

theorem doors_of_other (c : V → ℕ) (n : ℕ) (σ : Finset V)
    (himg : ¬ range (n + 1) ⊆ σ.image c) : (doorsOf c n σ).card = 0 := by
  rw [Finset.card_eq_zero, doorsOf, Finset.filter_eq_empty_iff]
  intro τ hτ hcon
  apply himg
  rw [← hcon]
  exact Finset.image_subset_image (Finset.mem_powersetCard.1 hτ).1

/-- A cell has an odd number of doors exactly when it is rainbow. -/
