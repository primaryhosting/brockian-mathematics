/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

lemma glue_apply_not_mem {n ℓ : ℕ} {σ : Fin n → Fin ℓ}
    (z : Fin n → Bool) (x0 : Fin ℓ → Bool) {i : Fin ℓ} (hi : ∀ k, σ k ≠ i) :
    glue σ z x0 i = x0 i := by
  simp only [glue]
  rw [dif_neg]
  rintro ⟨k, hk⟩
  exact hi k hk

/-- The seed-splitting equivalence: a seed together with a block assignment can be traded for
a block assignment together with a seed. -/
