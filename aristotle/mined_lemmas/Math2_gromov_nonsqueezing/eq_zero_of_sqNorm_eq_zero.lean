/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math2

/-- The standard symplectic form on `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2` (the pair `(i, 0)`, `(i, 1)` being the `i`-th conjugate pair). -/

lemma eq_zero_of_sqNorm_eq_zero {n : ℕ} {v : Fin n × Fin 2 → ℝ} (h : sqNorm v = 0) :
    v = 0 := by
  funext p
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun q (_ : q ∈ Finset.univ) => sq_nonneg (v q))).1 h
      p (Finset.mem_univ p)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

