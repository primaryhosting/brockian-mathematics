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

@[simp] lemma coe_term (k : Fin (2 ^ n)) :
    ((term k : Fin (2 * n + 2 ^ n + 1)) : ℕ) = 2 * n + (k : ℕ) := rfl

variable (f : Cube n → Bool) (e : Cube n ≃ Fin (2 ^ n))

/-- The conjunctions appearing in the final disjunction. -/
