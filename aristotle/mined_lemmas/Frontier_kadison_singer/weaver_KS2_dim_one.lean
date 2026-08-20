/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to come before any module docstring, so the header
-- above is reproduced verbatim as the module docstring immediately after the imports.)

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.letVarTypes true
set_option pp.funBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ComplexOrder InnerProductSpace

/-! ## States on a unital ⋆-algebra over `ℂ` -/

/-- A *state* on a unital `ℂ`-⋆-algebra `A`: a positive, normalized linear functional. -/
structure IsState {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) : Prop where
  /-- Positivity: `phi (a⋆ * a)` is a nonnegative real number. -/
  nonneg : ∀ a : A, 0 ≤ phi (star a * a)
  /-- Normalization. -/
  map_one : phi 1 = 1

namespace IsState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {phi : A →ₗ[ℂ] ℂ}


theorem weaver_KS2_dim_one {ι : Type*} [Fintype ι] [DecidableEq ι] {eps : ℝ} (v : ι → ℂ)
    (hle : ∀ i, ‖v i‖ ^ 2 ≤ eps) (hsum : ∑ i, ‖v i‖ ^ 2 = 1) :
    ∃ S : Finset ι,
      ∑ i ∈ S, ‖v i‖ ^ 2 ≤ (Real.sqrt (1 / 2) + Real.sqrt eps) ^ 2 ∧
      ∑ i ∈ Sᶜ, ‖v i‖ ^ 2 ≤ (Real.sqrt (1 / 2) + Real.sqrt eps) ^ 2 := by
  obtain ⟨S, h1, h2⟩ := exists_balanced_partition (fun i => ‖v i‖ ^ 2) hle hsum
  have hepsnn : 0 ≤ eps := by
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < ‖v i‖ ^ 2 :=
      Finset.exists_lt_of_sum_lt (by simpa using hsum.symm.le.trans_lt' (by norm_num))
    exact le_trans hi.le (hle i)
  have hkey : 1 / 2 + eps ≤ (Real.sqrt (1 / 2) + Real.sqrt eps) ^ 2 := by
    have h12 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have he : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt hepsnn
    have hnn : 0 ≤ Real.sqrt (1 / 2) * Real.sqrt eps :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [h12, he, hnn]
  exact ⟨S, h1.trans hkey, h2.trans hkey⟩

end Weaver

end Frontier

