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

lemma dgate_or (i : Fin (2 * n + 2 ^ n + 1)) (h1 : ¬ (i : ℕ) < n) (h2 : ¬ (i : ℕ) < 2 * n)
    (h3 : ¬ (i : ℕ) < 2 * n + 2 ^ n) :
    dgate f e i = Gate.or (terms f e) := by
  rw [dgate, dif_neg h1, dif_neg h2, dif_neg h3]

/-- The values of the gates of the DNF circuit on input `x`. -/
