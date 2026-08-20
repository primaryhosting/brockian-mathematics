import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma delta_apply (a x : Cube n) : delta a x = if x = a then 1 else 0 := by
  unfold delta
  by_cases h : x = a
  · subst h
    rw [if_pos rfl]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have := sgn_mul_self (x i)
    calc 2 + 2 * sgn (x i) * sgn (x i) = 2 + 2 * (sgn (x i) * sgn (x i)) := by ring
    _ = 1 := by rw [this]; decide
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : sgn (a i) * sgn (x i) = -1 := by
      cases hxa : a i <;> cases hxx : x i <;> simp_all
    calc 2 + 2 * sgn (a i) * sgn (x i) = 2 + 2 * (sgn (a i) * sgn (x i)) := by ring
    _ = 0 := by rw [this]; decide

