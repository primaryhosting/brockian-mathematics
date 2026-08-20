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

def dgate (i : Fin (2 * n + 2 ^ n + 1)) : Gate n (2 * n + 2 ^ n + 1) :=
  if h1 : (i : ℕ) < n then Gate.var ⟨i, h1⟩
  else if h2 : (i : ℕ) < 2 * n then Gate.not ⟨(i : ℕ) - n, by omega⟩
  else if h3 : (i : ℕ) < 2 * n + 2 ^ n then
    Gate.and (lits (e.symm ⟨(i : ℕ) - 2 * n, by omega⟩))
  else Gate.or (terms f e)

