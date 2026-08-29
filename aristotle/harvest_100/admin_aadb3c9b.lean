/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

/-- The CHSH combination of four correlation values. -/
def CHSH (E : Bool → Bool → ℝ) : ℝ :=
  E false false + E false true + E true false - E true true

/-- The correlation function produced by a local hidden-variable model: a hidden variable
`w : Ω` distributed according to `p`, with Alice's outcome `A i w` depending only on her
setting `i`, and Bob's outcome `B j w` only on his setting `j`. -/
def LHVCorr {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (A B : Bool → Ω → ℝ) : Bool → Bool → ℝ :=
  fun i j => ∑ w : Ω, p w * (A i w * B j w)

/-- Pointwise CHSH bound for outcomes bounded by 1. -/
theorem chsh_pointwise {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : |a₁| ≤ 1) (ha₂ : |a₂| ≤ 1)
    (hb₁ : |b₁| ≤ 1) (hb₂ : |b₂| ≤ 1) :
    |a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂| ≤ 2 := by
  rw [abs_le] at ha₁ ha₂ hb₁ hb₂ ⊢
  constructor <;>
    nlinarith [mul_nonneg (sub_nonneg.2 ha₁.2) (sub_nonneg.2 hb₁.2),
      mul_nonneg (sub_nonneg.2 ha₁.2) (sub_nonneg.2 hb₂.2),
      mul_nonneg (sub_nonneg.2 ha₂.2) (sub_nonneg.2 hb₁.2),
      mul_nonneg (sub_nonneg.2 ha₂.2) (sub_nonneg.2 hb₂.2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₁) (by linarith : (0:ℝ) ≤ 1 + b₁),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₁) (by linarith : (0:ℝ) ≤ 1 + b₂),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₂) (by linarith : (0:ℝ) ≤ 1 + b₁),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₂) (by linarith : (0:ℝ) ≤ 1 + b₂),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₁) (sub_nonneg.2 hb₁.2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₁) (sub_nonneg.2 hb₂.2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₂) (sub_nonneg.2 hb₁.2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a₂) (sub_nonneg.2 hb₂.2),
      mul_nonneg (sub_nonneg.2 ha₁.2) (by linarith : (0:ℝ) ≤ 1 + b₁),
      mul_nonneg (sub_nonneg.2 ha₁.2) (by linarith : (0:ℝ) ≤ 1 + b₂),
      mul_nonneg (sub_nonneg.2 ha₂.2) (by linarith : (0:ℝ) ≤ 1 + b₁),
      mul_nonneg (sub_nonneg.2 ha₂.2) (by linarith : (0:ℝ) ≤ 1 + b₂)]

/-- **CHSH inequality for local hidden-variable models.**  Any local hidden-variable model
with outcomes in `[-1, 1]` satisfies `|CHSH| ≤ 2`. -/
theorem chsh_le_two {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (A B : Bool → Ω → ℝ)
    (hp₀ : ∀ w, 0 ≤ p w) (hp₁ : ∑ w : Ω, p w = 1)
    (hA : ∀ i w, |A i w| ≤ 1) (hB : ∀ j w, |B j w| ≤ 1) :
    |CHSH (LHVCorr p A B)| ≤ 2 := by
  have key : CHSH (LHVCorr p A B)
      = ∑ w : Ω, p w * (A false w * B false w + A false w * B true w
          + A true w * B false w - A true w * B true w) := by
    simp only [CHSH, LHVCorr, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [key]
  calc |∑ w : Ω, p w * (A false w * B false w + A false w * B true w
          + A true w * B false w - A true w * B true w)|
      ≤ ∑ w : Ω, |p w * (A false w * B false w + A false w * B true w
          + A true w * B false w - A true w * B true w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : Ω, p w * 2 := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [abs_mul, abs_of_nonneg (hp₀ w)]
        exact mul_le_mul_of_nonneg_left
          (chsh_pointwise (hA false w) (hA true w) (hB false w) (hB true w)) (hp₀ w)
    _ = 2 := by rw [← Finset.sum_mul, hp₁, one_mul]

/-- Alice's two measurement angles in the quantum (singlet) setup. -/
noncomputable def alphaAngle : Bool → ℝ := fun i => if i then Real.pi / 2 else 0

/-- Bob's two measurement angles in the quantum (singlet) setup. -/
noncomputable def betaAngle : Bool → ℝ := fun j => if j then -(Real.pi / 4) else Real.pi / 4

/-- The quantum correlation predicted for two spin measurements at the given angles. -/
noncomputable def QuantumCorr : Bool → Bool → ℝ :=
  fun i j => Real.cos (alphaAngle i - betaAngle j)

/-- The quantum prediction violates the classical CHSH bound: its CHSH value is `2√2`. -/
theorem chsh_quantum : CHSH QuantumCorr = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, h4]
  simp only [CHSH, QuantumCorr, alphaAngle, betaAngle, if_true, if_false]
  have e1 : (0 : ℝ) - Real.pi / 4 = -(Real.pi / 4) := by ring
  have e2 : (0 : ℝ) - -(Real.pi / 4) = Real.pi / 4 := by ring
  have e3 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  have e4 : Real.pi / 2 - -(Real.pi / 4) = 3 * Real.pi / 4 := by ring
  rw [e1, e2, e3, e4, Real.cos_neg, h4, h34]
  ring

theorem two_lt_two_sqrt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

/-- **Bell's theorem.**  No local hidden-variable model reproduces the quantum-mechanical
correlations: for any finite hidden-variable space with a probability weight `p` and
outcome functions `A`, `B` taking values in `[-1, 1]` (Alice's depending only on her setting,
Bob's only on his), the resulting correlations cannot equal the quantum predictions
`QuantumCorr`, because the latter have CHSH value `2√2 > 2` while every local model obeys
`|CHSH| ≤ 2`. -/
theorem bell_theorem {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (A B : Bool → Ω → ℝ)
    (hp₀ : ∀ w, 0 ≤ p w) (hp₁ : ∑ w : Ω, p w = 1)
    (hA : ∀ i w, |A i w| ≤ 1) (hB : ∀ j w, |B j w| ≤ 1) :
    ∃ i j, LHVCorr p A B i j ≠ QuantumCorr i j := by
  by_contra hcon
  push_neg at hcon
  have hEq : CHSH (LHVCorr p A B) = CHSH QuantumCorr := by
    simp only [CHSH, hcon]
  have hle : |CHSH (LHVCorr p A B)| ≤ 2 := chsh_le_two p A B hp₀ hp₁ hA hB
  rw [hEq, chsh_quantum] at hle
  have := two_lt_two_sqrt_two
  have h2 : (2 : ℝ) * Real.sqrt 2 ≤ 2 := le_trans (le_abs_self _) hle
  linarith

end Frontier

import Mathlib

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

