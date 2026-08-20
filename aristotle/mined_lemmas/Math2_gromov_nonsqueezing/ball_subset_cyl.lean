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

theorem ball_subset_cyl {n : ℕ} {r R : ℝ} (h : r ≤ R) :
    (LinearEquiv.refl ℝ (V (n + 1))) '' ball (n + 1) r ⊆ cyl n R := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [ball, Set.mem_setOf_eq] at hz
  have hnorm : ‖z‖ ^ 2 = ∑ p, (z.ofLp p) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
    exact Finset.sum_congr rfl (fun p _ => (sq (z.ofLp p)).symm)
  have hpair : ((0 : Fin (n + 1)), (0 : Fin 2)) ≠ ((0 : Fin (n + 1)), (1 : Fin 2)) := by
    simp
  have hle : (z.ofLp ((0 : Fin (n + 1)), (0 : Fin 2))) ^ 2
      + (z.ofLp ((0 : Fin (n + 1)), (1 : Fin 2))) ^ 2 ≤ ∑ p, (z.ofLp p) ^ 2 := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun p : Fin (n + 1) × Fin 2 => (z.ofLp p) ^ 2)
      (Finset.subset_univ ({((0 : Fin (n + 1)), (0 : Fin 2)),
        ((0 : Fin (n + 1)), (1 : Fin 2))} : Finset (Fin (n + 1) × Fin 2)))
      (fun p _ _ => sq_nonneg _)
    rwa [Finset.sum_pair hpair] at hsum
  simp only [LinearEquiv.refl_apply, cyl, Set.mem_setOf_eq]
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hz2 : ‖z‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg z]
  nlinarith [hle, hnorm, hz2]

end Math2

