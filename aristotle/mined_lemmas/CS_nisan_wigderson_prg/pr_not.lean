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

lemma pr_not {α : Type*} [Fintype α] [Nonempty α] (q r : α → Bool) :
    (pr fun a => (!q a) == r a) = 1 - pr fun a => q a == r a := by
  unfold pr
  rw [eq_sub_iff_add_eq, ← Finset.expect_add_distrib]
  rw [show (1 : ℝ) = 𝔼 _a : α, (1 : ℝ) from (Finset.expect_const univ_nonempty 1).symm]
  refine Finset.expect_congr rfl fun a _ => ?_
  cases hq : q a <;> cases hr : r a <;> simp [ind, hq, hr]

/-- Fixing the seed bits outside the `t`-th block and the random bits turns the
next-bit predictor into a genuine Nisan–Wigderson predictor for `f`. -/
