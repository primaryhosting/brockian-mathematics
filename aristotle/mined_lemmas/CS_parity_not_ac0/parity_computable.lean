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

theorem parity_computable (n : ℕ) : ∃ c : Circuit n, c.DepthLe 2 ∧ c.Computes (parity n) :=
  exists_depth_two_circuit n (parity n)

/-- `AC⁰` is not empty: the constantly false family belongs to it. -/
