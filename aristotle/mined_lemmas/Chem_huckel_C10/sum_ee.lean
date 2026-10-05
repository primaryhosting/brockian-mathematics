/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₁₀` are `2 cos (2πk/10)`, `k = 0, …, 9`:
the characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 10`
factors as `∏ k, (X - 2 cos (2πk/10))`.
-/

namespace Chem

open Polynomial Matrix

/-! ### Arithmetic in `Fin 10`

`Fin 10` carries the modular addition and multiplication of `ZMod 10`, but Mathlib does not
register a `CommRing` instance on it, so `ring` is unavailable; the few needed ring identities
are checked by `decide`. -/

set_option maxRecDepth 10000 in

lemma sum_ee (m : Fin 10) : ∑ k : Fin 10, ee (k * m) = if m = 0 then 10 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [ee_zero]
  · simp only [hm, if_false]
    set S := ∑ k : Fin 10, ee (k * m) with hS
    have key : ee m * S = S := by
      have h2 : ee m * S = ∑ k : Fin 10, ee ((k + 1) * m) := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [add_mul, one_mul, ee_add]
        ring
      rw [h2, hS]
      exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 10))
        (fun k => ee ((k + 1) * m)) (fun k => ee (k * m)) (fun _ => rfl)
    have h1 : ee m - 1 ≠ 0 := sub_ne_zero.mpr fun h => hm ((ee_eq_one_iff m).mp h)
    have h3 : (ee m - 1) * S = 0 := by linear_combination key
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h1
    · exact h

/-- The eigenvalue attached to index `k`. -/
