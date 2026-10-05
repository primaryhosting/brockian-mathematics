/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `5` elements.
A `node (a, b) l r` compares the input entries at positions `a` and `b`, continuing in `l`
if the comparison oracle answers `true` and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 × Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Worst-case number of comparisons performed by the tree. -/

theorem oracle_injective {q p : Equiv.Perm (Fin 5)} (h : ∀ a b, oracle q a b = oracle p a b) :
    q = p := by
  have key : ∀ e : Equiv.Perm (Fin 5),
      (∀ x y : Fin 5, decide (e x ≤ e y) = decide (x ≤ y)) → e = 1 := by
    decide
  have he : (q * p⁻¹ : Equiv.Perm (Fin 5)) = 1 := by
    refine key _ fun x y => ?_
    have := h (p⁻¹ x) (p⁻¹ y)
    simpa [oracle, Equiv.Perm.mul_apply] using this
  have := congrArg (fun e : Equiv.Perm (Fin 5) => e * p) he
  simpa [mul_assoc] using this

/-- Correctness of `build`: if the true arrangement `p` is among the candidates and the queried
comparisons suffice to single it out, the tree outputs `p`. -/
