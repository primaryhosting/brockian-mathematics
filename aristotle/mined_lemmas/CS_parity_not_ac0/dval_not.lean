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

lemma dval_not (x : Cube n) (j : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (j : ℕ) < n)
    (h2 : (j : ℕ) < 2 * n) : dval f e x j = !(x ⟨(j : ℕ) - n, by omega⟩) := by
  rw [dval, dif_neg h1, dif_pos h2]

