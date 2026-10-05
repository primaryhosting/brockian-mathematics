/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Filter Topology

namespace Math

/-- Every nonzero complex number has an `n`-th root for `n > 0`
(elementary consequence of the surjectivity of `Complex.exp` onto `ℂ \ {0}`). -/

theorem exists_pow_eq_of_ne_zero {z : ℂ} (hz : z ≠ 0) {n : ℕ} (hn : 0 < n) :
    ∃ u : ℂ, u ^ n = z := by
  refine ⟨Complex.exp (Complex.log z / n), ?_⟩
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), Complex.exp_log hz]

/-- Key step of the d'Alembert–Argand argument: if `t(0) ≠ 0` and `k > 0`, then the value `1`
of the function `w ↦ 1 + wᵏ t(w)` at `w = 0` is not a local minimum of its modulus. -/
