/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

lemma pick_fiber {n : ℕ} (s x y : Vec n) (h : pick s x = pick s y) : y = x ∨ y = x + s := by
  have hss : ∀ v : Vec n, v + s + s = v := by
    intro v; rw [add_assoc, vec_add_self, add_zero]
  rcases pick_eq_or s x with hx | hx <;> rcases pick_eq_or s y with hy | hy <;>
    rw [hx, hy] at h
  · exact Or.inl h.symm
  · right
    have := congrArg (fun v => v + s) h
    simpa [hss] using this.symm
  · exact Or.inr h.symm
  · exact Or.inl (add_right_cancel h).symm

/-- **Classical lower bound.**  A deterministic classical decision tree of depth `d` that
outputs the hidden shift of every Simon function must satisfy `2 ^ n ≤ d ^ 2 + 2`.

The argument is the standard adversary/birthday argument: run the tree on the injective
oracle `id`; if the tree is shallow, some nonzero shift `s` is neither the produced answer
nor a difference of two queried points, and then an actual Simon function with shift `s`
can be built which agrees with `id` on all queried points, fooling the tree. -/
