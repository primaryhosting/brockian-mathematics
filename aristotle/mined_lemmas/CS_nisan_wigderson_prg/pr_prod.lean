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

lemma pr_prod {α β : Type*} [Fintype α] [Fintype β] (p : α × β → Bool) :
    pr p = 𝔼 a, 𝔼 b, ind (p (a, b)) := by
  refine Eq.trans ?_ (Finset.expect_product' univ univ fun a b => ind (p (a, b)))
  rw [Finset.univ_product_univ]
  rfl

/-! ### The hybrid argument -/

