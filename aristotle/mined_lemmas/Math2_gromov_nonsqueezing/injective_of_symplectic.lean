import Mathlib
/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators RealInnerProductSpace

namespace Math2

/-- The standard symplectic vector space `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2`: the pair `(i, 0), (i, 1)` is the `i`-th conjugate coordinate pair. -/
abbrev SympSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form on `ℝ^{2n}`. -/

lemma injective_of_symplectic {n : ℕ} {A : SympSpace n →ₗ[ℝ] SympSpace n}
    (hA : IsLinearSymplectic A) : Function.Injective A := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_omegaForm_eq_zero fun y => ?_
  rw [← hA x y, hx]
  simp [omegaForm]

