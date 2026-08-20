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
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-! ## The standard symplectic vector space `ℝ^{2n}`

We model `ℝ^{2n}` as the Euclidean space indexed by `Fin n × Fin 2`, where for each
`i : Fin n` the coordinate `(i,0)` is the position `x i` and `(i,1)` is the momentum `y i`.
-/

/-- The standard `2n`-dimensional Euclidean/symplectic vector space. -/
abbrev V (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form `ω(u,v) = ∑ i, (u_{x i} v_{y i} - u_{y i} v_{x i})`. -/

lemma gram_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a c b : E) (h1 : ⟪a, c⟫ = 0) (h2 : ‖c‖ = ‖a‖) :
    ⟪c, b⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hc : c = 0 := by rw [← norm_eq_zero, h2]; simp
    simp [hc]
  have hA : (0:ℝ) < ‖a‖ ^ 2 := by positivity
  set A : ℝ := ‖a‖ ^ 2 with hAdef
  set p : E := b - (⟪a, b⟫ / A) • a - (⟪c, b⟫ / A) • c with hp
  have h0 : (0:ℝ) ≤ ⟪p, p⟫ := real_inner_self_nonneg
  have hcc : ⟪c, c⟫ = A := by rw [real_inner_self_eq_norm_sq, h2]
  have haa : ⟪a, a⟫ = A := real_inner_self_eq_norm_sq a
  have hbb : ⟪b, b⟫ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
  have hca : ⟪c, a⟫ = 0 := by rw [real_inner_comm]; exact h1
  have hexp : ⟪p, p⟫ = ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 / A - ⟪c, b⟫ ^ 2 / A := by
    simp only [hp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      h1, hca, hcc, haa, hbb, real_inner_comm b a, real_inner_comm b c]
    field_simp
    ring
  rw [hexp] at h0
  have h0' : ⟪a, b⟫ ^ 2 / A * A + ⟪c, b⟫ ^ 2 / A * A ≤ ‖b‖ ^ 2 * A :=
    by nlinarith [mul_nonneg h0 hA.le]
  rw [div_mul_cancel₀ _ hA.ne', div_mul_cancel₀ _ hA.ne'] at h0'
  linarith

/-- **Key intermediate lemma.**  If the Gram determinant of `a, b` is at least `1`,
then some unit vector `w` satisfies `⟪a,w⟫² + ⟪b,w⟫² ≥ 1`; i.e. the image of the unit
ball under `z ↦ (⟪a,z⟫, ⟪b,z⟫)` is not contained in any disc of radius `< 1`. -/
