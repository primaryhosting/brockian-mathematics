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

lemma injective_of_isSymplectic {n : ℕ}
    {Φ : (Fin n × Fin 2 → ℝ) →ₗ[ℝ] (Fin n × Fin 2 → ℝ)} (hΦ : IsSymplectic Φ) :
    Function.Injective Φ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h0 : symplecticForm u (jvec u) = 0 := by
    rw [← hΦ u (jvec u), hu]
    simp [symplecticForm]
  exact eq_zero_of_sqNorm_eq_zero (by rw [← symplecticForm_self_jvec, h0])

/-- **Gromov's nonsqueezing theorem** (linear case).

If a linear symplectomorphism of `ℝ^{2(n+1)}` maps the open ball of radius `r > 0`
into the open symplectic cylinder of radius `R ≥ 0` (the cylinder over the first
conjugate coordinate plane), then `r ≤ R`. -/
