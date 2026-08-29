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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-! ## Setup: the standard symplectic vector space -/

/-- The standard symplectic phase space `ℝ^{2n}`, with coordinates indexed by `ι ⊕ ι`:
`Sum.inl i` is the `i`-th position coordinate `qᵢ`, and `Sum.inr i` the `i`-th momentum
coordinate `pᵢ`.  It carries the standard Euclidean inner product. -/
abbrev Phase (ι : Type*) [Fintype ι] := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (qᵢ(x) pᵢ(y) - pᵢ(x) qᵢ(y))`. -/

lemma one_le_gram_of_omegaForm_eq_one {u v : Phase ι} (hu : u ≠ 0) (h : omegaForm u v = 1) :
    1 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  set c : ℝ := ⟪u, v⟫ / ‖u‖ ^ 2 with hc
  set w : Phase ι := v - c • u with hw
  have h1 : ⟪Jmap u, w⟫ = 1 := by
    rw [hw, inner_sub_right, real_inner_smul_right, inner_Jmap, inner_Jmap, omegaForm_self, h]
    ring
  have h2 : ⟪Jmap u, w⟫ ≤ ‖Jmap u‖ * ‖w‖ := real_inner_le_norm _ _
  have h3 : 1 ≤ ‖u‖ * ‖w‖ := by rw [norm_Jmap] at h2; linarith [h1 ▸ h2]
  have h4 : ‖u‖ ^ 2 * ‖w‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 :=
    norm_sq_mul_norm_proj_sq u v hu
  nlinarith [norm_nonneg u, norm_nonneg w]

/-- If `ω(u, v) = 1`, there is a unit vector `x` with `⟪u, x⟫² + ⟪v, x⟫² ≥ 1`. -/
