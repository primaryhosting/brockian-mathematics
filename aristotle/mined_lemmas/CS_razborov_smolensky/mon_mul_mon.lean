import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem mon_mul_mon {n : ℕ} (S T : Finset (Fin n)) :
    (mon S : Cube n → F) * mon T = mon (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, mon_eq_ite]
  by_cases hS : ∀ i ∈ S, x i = true <;> by_cases hT : ∀ i ∈ T, x i = true <;>
    simp_all [Finset.mem_union] <;> grind

variable (F)

/-- The set of monomials of degree at most `d`. -/
