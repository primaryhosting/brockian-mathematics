/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem Statistics.eq_of_sign_eq {a b : Statistics} (h : a.sign = b.sign) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | (exfalso; simp [Statistics.sign] at h; norm_num at h)

/-! ## Wightman-type field data

A `WightmanField` packages the structural input of the spin–statistics theorem in the
Wightman framework: a Hilbert space of states with a vacuum vector, a family of smeared
field operators indexed by test functions together with their adjoints and (spacetime)
supports, a spin and a statistics, and the following properties.

* `locality` : at spacelike separation the fields obey the (anti)commutation relation
  dictated by their statistics.
* `jost` : *weak local commutativity*. At spacelike separation (Jost points) the analytic
  continuation of the two-point function relates the two orderings by the factor
  `(-1)^{2s}`.  This is the consequence of Lorentz covariance (equivalently PCT) and of
  the analyticity of the Wightman functions in the extended tube.
* `analytic` : *uniqueness of analytic continuation*. If the two-point function
  `⟪Ω, φ(g)^* φ(f) Ω⟫` vanishes for all spacelike separated configurations, then it
  vanishes identically, in particular at coincident arguments.
* `separating` : *Reeh–Schlieder*. The vacuum is separating for the field operators.
-/
structure WightmanField (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (TF : Type*) where
  /-- The spacetime support of a smeared field. -/
  supp : TF → Set (Fin 4 → ℝ)
  /-- The smeared field operator. -/
  field : TF → (H →L[ℂ] H)
  /-- The adjoint of the smeared field operator. -/
  fieldAdj : TF → (H →L[ℂ] H)
  /-- `fieldAdj f` is the adjoint of `field f`. -/
  adj_spec : ∀ f x y, ⟪fieldAdj f x, y⟫_ℂ = ⟪x, field f y⟫_ℂ
  /-- The vacuum vector. -/
  vacuum : H
  /-- Twice the spin of the field. -/
  twiceSpin : ℕ
  /-- The statistics with which the field is quantized. -/
  stat : Statistics
  /-- Locality: the fields (anti)commute at spacelike separation according to `stat`. -/
  locality : ∀ f g, SpacelikeSeparated (supp f) (supp g) →
      (field f) ∘L (fieldAdj g) = stat.sign • ((fieldAdj g) ∘L (field f))
  /-- Weak local commutativity at Jost points, from Lorentz covariance. -/
  jost : ∀ f g, SpacelikeSeparated (supp f) (supp g) →
      ⟪vacuum, (field f) (fieldAdj g vacuum)⟫_ℂ
        = (-1 : ℂ) ^ twiceSpin * ⟪vacuum, (fieldAdj g) (field f vacuum)⟫_ℂ
  /-- Uniqueness of analytic continuation for the two-point function. -/
  analytic : (∀ f g, SpacelikeSeparated (supp f) (supp g) →
        ⟪vacuum, (fieldAdj g) (field f vacuum)⟫_ℂ = 0) →
      ∀ f, ⟪vacuum, (fieldAdj f) (field f vacuum)⟫_ℂ = 0
  /-- Reeh–Schlieder: the vacuum is separating. -/
  separating : ∀ f, field f vacuum = 0 → field f = 0

namespace WightmanField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {TF : Type*}
  (Φ : WightmanField H TF)

/-- Positivity: the vacuum expectation value `⟪Ω, φ(f)^* φ(f) Ω⟫` is the squared norm of
`φ(f) Ω`. -/
