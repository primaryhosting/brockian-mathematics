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


theorem exists_balanced_partition {ι : Type*} [Fintype ι] [DecidableEq ι] {eps : ℝ} (a : ι → ℝ)
    (hle : ∀ i, a i ≤ eps) (hsum : ∑ i, a i = 1) :
    ∃ S : Finset ι, ∑ i ∈ S, a i ≤ 1 / 2 + eps ∧ ∑ i ∈ Sᶜ, a i ≤ 1 / 2 + eps := by
  classical
  set P : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter (fun S => ∑ i ∈ S, a i ≤ 1 / 2) with hP
  have hPne : P.Nonempty := ⟨∅, by simp [hP]⟩
  obtain ⟨S, hSP, hSmax⟩ := P.exists_max_image (fun S => ∑ i ∈ S, a i) hPne
  have hS : ∑ i ∈ S, a i ≤ 1 / 2 := by
    have := Finset.mem_filter.mp hSP
    simpa using this.2
  have hcompl : ∑ i ∈ S, a i + ∑ i ∈ Sᶜ, a i = 1 := by
    rw [Finset.sum_add_sum_compl, hsum]
  have hlow : 1 / 2 - eps ≤ ∑ i ∈ S, a i := by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < ∑ i ∈ Sᶜ, a i := by linarith
    obtain ⟨i, hiS, hai⟩ : ∃ i ∈ Sᶜ, 0 < a i :=
      Finset.exists_lt_of_sum_lt (by simpa using hpos)
    have hinotS : i ∉ S := by simpa using hiS
    have hins : ∑ j ∈ insert i S, a j = a i + ∑ j ∈ S, a j := Finset.sum_insert hinotS
    have hmem : insert i S ∈ P := by
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      rw [hins]
      have := hle i
      linarith
    have hmax := hSmax _ hmem
    rw [hins] at hmax
    linarith
  exact ⟨S, by linarith, by linarith⟩

/-- **Weaver's `KS₂` in dimension one** (the `d = 1` case of the Marcus–Spielman–Srivastava
theorem). Given scalars `v i` with `∑ i, ‖v i‖ ^ 2 = 1` and `‖v i‖ ^ 2 ≤ eps`, the index set
splits into two parts, each of total weight at most `(1 / √2 + √eps) ^ 2`. -/
