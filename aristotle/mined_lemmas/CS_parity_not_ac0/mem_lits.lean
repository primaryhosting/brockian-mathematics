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

lemma mem_lits {a : Cube n} {j : Fin (2 * n + 2 ^ n + 1)} (h : j ∈ lits a) :
    ∃ k : Fin n, j = lit a k := by
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp h).2
  exact ⟨k, Fin.ext hk⟩

/-- The gate index of the `k`-th conjunction. -/
