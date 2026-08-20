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

def Circuit.DepthLe (c : Circuit n) (d : ℕ) : Prop :=
  ∃ lev : Fin c.size → ℕ, (∀ i, lev i ≤ d) ∧
    ∀ i j, j ∈ (c.gate i).refs → lev j + (c.gate i).cost ≤ lev i

/-- The parity function on `n` bits. -/
