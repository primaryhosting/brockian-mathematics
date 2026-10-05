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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- The symplectic vector space `ℝ^{2n}`, modelled as the Euclidean space indexed by `ι ⊕ ι`:
the `Sum.inl` coordinates are the "positions" and the `Sum.inr` coordinates the "momenta". -/
abbrev SymplecticSpace (ι : Type*) [Fintype ι] : Type _ := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form on `ℝ^{2n} = ℝ^ι × ℝ^ι`,
`ω(u, v) = ∑ i, (u_i v_{n+i} - u_{n+i} v_i)`. -/

theorem ball_subset_cylinder [DecidableEq ι] (i₀ : ι) (r : ℝ) (hr : 0 < r) :
    (LinearEquiv.refl ℝ (SymplecticSpace ι)) '' Metric.ball (0 : SymplecticSpace ι) r ⊆
      cylinder i₀ r := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_ball_zero_iff] at hx
  have hnorm : ‖x‖ ^ 2 = ∑ j : ι ⊕ ι, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [sq_abs]
  have hsub : ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : ∑ j ∈ ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)), (x j) ^ 2 =
      (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 :=
    Finset.sum_pair (by simp)
  have hle : (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnorm, ← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
  have : ‖x‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg x]
  simpa [cylinder] using lt_of_le_of_lt hle this

end Math2

