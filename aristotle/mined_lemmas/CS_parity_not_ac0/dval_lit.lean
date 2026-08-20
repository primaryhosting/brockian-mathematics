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

lemma dval_lit (x a : Cube n) (k : Fin n) :
    dval f e x (lit a k) = (if a k then x k else !(x k)) := by
  have hk := k.2
  by_cases hak : a k
  · have h1 : ((lit a k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = (k : ℕ) := by simp [litIdx, hak]
    simp only [dval, h1, dif_pos hk, hak, if_true, Fin.eta]
  · have h1 : ((lit a k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = n + (k : ℕ) := by simp [litIdx, hak]
    have h2 : ¬ (n + (k : ℕ) < n) := by omega
    have h3 : n + (k : ℕ) < 2 * n := by omega
    simp only [dval, h1, dif_neg h2, dif_pos h3, hak, Bool.false_eq_true, if_false]
    congr 2
    exact Fin.ext (by simp)

