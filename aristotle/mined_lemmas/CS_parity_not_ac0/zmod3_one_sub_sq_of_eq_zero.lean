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

lemma zmod3_one_sub_sq_of_eq_zero (a : ZMod 3) (h : a = 0) : 1 - a ^ 2 = 1 := by
  subst h; norm_num

/-- Halving lemma: if some coefficient in `s` equals `1`, then at most half of
all subsets `U` make `∑_{j ∈ s ∩ U} z j` vanish. -/
