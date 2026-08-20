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

lemma dval_term (x : Cube n) (k : Fin (2 ^ n)) :
    dval f e x (term k) = decide (x = e.symm k) := by
  have hk := k.2
  have h1 : ¬ (2 * n + (k : ℕ) < n) := by omega
  have h2 : ¬ (2 * n + (k : ℕ) < 2 * n) := by omega
  have h3 : 2 * n + (k : ℕ) < 2 * n + 2 ^ n := by omega
  simp only [dval, coe_term, dif_neg h1, dif_neg h2, dif_pos h3]
  congr 3
  exact Fin.ext (by simp)

end DNF

open DNF in
open DNF in
/-- **Every Boolean function is computed by a circuit of depth 2.** -/
