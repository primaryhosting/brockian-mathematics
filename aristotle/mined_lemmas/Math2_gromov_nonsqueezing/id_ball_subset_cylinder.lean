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

theorem id_ball_subset_cylinder [DecidableEq ι] (i₀ : ι) (r : ℝ) :
    (LinearEquiv.refl ℝ (Phase ι)) '' symplecticBall r ⊆ symplecticCylinder i₀ r := by
  rintro y ⟨x, hx, rfl⟩
  have hxr : ‖x‖ < r := hx
  have hnorm : ‖x‖ ^ 2 = ∑ k, (x k) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => sq_abs _
  have hpair : (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2
      = ∑ k ∈ ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)), (x k) ^ 2 := by
    rw [Finset.sum_pair (by simp)]
  have hle : ∑ k ∈ ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)), (x k) ^ 2 ≤ ∑ k, (x k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _
  have : (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hpair, hnorm]; exact hle
  have hxnn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  show (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 < r ^ 2
  nlinarith

end Math2

