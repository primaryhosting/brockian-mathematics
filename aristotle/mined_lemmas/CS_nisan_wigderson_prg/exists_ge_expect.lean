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

lemma exists_ge_expect {α : Type*} [Fintype α] [Nonempty α] (F : α → ℝ) :
    ∃ a, (𝔼 x, F x) ≤ F a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (univ : Finset α) F univ_nonempty
  exact ⟨a, Finset.expect_le univ_nonempty fun x _ => ha x (mem_univ x)⟩

/-- Averaging over a product type. -/
