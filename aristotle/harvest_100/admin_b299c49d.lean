/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real

namespace Frontier

/-- **Pointwise CHSH bound.** For real numbers of absolute value at most `1`,
the CHSH combination `a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂` has absolute value at most `2`. -/
theorem chsh_pointwise (a1 a2 b1 b2 : ℝ) (h1 : |a1| ≤ 1) (h2 : |a2| ≤ 1)
    (h3 : |b1| ≤ 1) (h4 : |b2| ≤ 1) :
    |a1 * b1 + a1 * b2 + a2 * b1 - a2 * b2| ≤ 2 := by
  rw [abs_le] at *
  obtain ⟨p1, q1⟩ := h1; obtain ⟨p2, q2⟩ := h2; obtain ⟨p3, q3⟩ := h3; obtain ⟨p4, q4⟩ := h4
  constructor <;>
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a1) (by linarith : (0:ℝ) ≤ 1 + b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a1) (by linarith : (0:ℝ) ≤ 1 + b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 - b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 + b1),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a2) (by linarith : (0:ℝ) ≤ 1 + b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 - b2),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 + a2) (by linarith : (0:ℝ) ≤ 1 + b2)]

section LHV

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The correlation predicted by a local hidden-variable model with hidden-variable
distribution `μ` and local response functions `A i`, `B j`. -/
noncomputable def lhvCorr (A B : Ω → ℝ) : ℝ := ∫ ω, A ω * B ω ∂μ

private theorem integrable_prod {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hA1 : ∀ ω, |A ω| ≤ 1) (hB1 : ∀ ω, |B ω| ≤ 1) :
    Integrable (fun ω => A ω * B ω) μ := by
  refine ⟨(hA.mul hB).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards with ω
  have := abs_mul (A ω) (B ω)
  have h1 : |A ω| ≤ 1 := hA1 ω
  have h2 : |B ω| ≤ 1 := hB1 ω
  have h0 : (0:ℝ) ≤ |A ω| := abs_nonneg _
  simp only [Real.norm_eq_abs, this]
  nlinarith

/-- **The CHSH inequality for local hidden-variable models.**
If `A₁, A₂` (Alice) and `B₁, B₂` (Bob) are measurable `[-1,1]`-valued response functions of a
hidden variable distributed according to a probability measure `μ`, then the CHSH combination
of the resulting correlations is bounded by `2` in absolute value. -/
theorem chsh_classical (A1 A2 B1 B2 : Ω → ℝ)
    (hA1 : Measurable A1) (hA2 : Measurable A2) (hB1 : Measurable B1) (hB2 : Measurable B2)
    (bA1 : ∀ ω, |A1 ω| ≤ 1) (bA2 : ∀ ω, |A2 ω| ≤ 1)
    (bB1 : ∀ ω, |B1 ω| ≤ 1) (bB2 : ∀ ω, |B2 ω| ≤ 1) :
    |lhvCorr μ A1 B1 + lhvCorr μ A1 B2 + lhvCorr μ A2 B1 - lhvCorr μ A2 B2| ≤ 2 := by
  have i11 := integrable_prod μ hA1 hB1 bA1 bB1
  have i12 := integrable_prod μ hA1 hB2 bA1 bB2
  have i21 := integrable_prod μ hA2 hB1 bA2 bB1
  have i22 := integrable_prod μ hA2 hB2 bA2 bB2
  have s1 : Integrable (fun ω => A1 ω * B1 ω + A1 ω * B2 ω) μ := i11.add i12
  have s2 : Integrable (fun ω => A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω) μ := s1.add i21
  have hint : Integrable (fun ω => A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) μ :=
    s2.sub i22
  have hsplit : ∫ ω, (A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) ∂μ
      = lhvCorr μ A1 B1 + lhvCorr μ A1 B2 + lhvCorr μ A2 B1 - lhvCorr μ A2 B2 := by
    rw [integral_sub s2 i22, integral_add s1 i21, integral_add i11 i12]
    rfl
  have hbd : ∀ ω, |A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω| ≤ 2 := fun ω =>
    chsh_pointwise _ _ _ _ (bA1 ω) (bA2 ω) (bB1 ω) (bB2 ω)
  have hup : ∫ ω, (A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) ∂μ ≤ 2 := by
    have := integral_mono hint (integrable_const (2:ℝ))
      (fun ω => (abs_le.mp (hbd ω)).2)
    simpa using this
  have hlow : -2 ≤ ∫ ω, (A1 ω * B1 ω + A1 ω * B2 ω + A2 ω * B1 ω - A2 ω * B2 ω) ∂μ := by
    have := integral_mono (integrable_const (-2:ℝ)) hint
      (fun ω => (abs_le.mp (hbd ω)).1)
    simpa using this
  rw [← hsplit, abs_le]
  exact ⟨hlow, hup⟩

end LHV

/-- Alice's two measurement angles. -/
noncomputable def aliceAngle : Bool → ℝ
  | false => 0
  | true => π / 2

/-- Bob's two measurement angles. -/
noncomputable def bobAngle : Bool → ℝ
  | false => π / 4
  | true => -(π / 4)

/-- The quantum-mechanical correlation `cos (α - β)` for two spin measurements at angles
`α` and `β` (in the appropriate state). -/
noncomputable def quantumCorr (i j : Bool) : ℝ := Real.cos (aliceAngle i - bobAngle j)

/-- The quantum CHSH value for these four settings is `2√2`. -/
theorem quantum_chsh_value :
    quantumCorr false false + quantumCorr false true + quantumCorr true false
      - quantumCorr true true = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (π / 2 - -(π / 4)) = -(Real.sqrt 2 / 2) := by
    have : π / 2 - -(π / 4) = π - π / 4 := by ring
    rw [this, Real.cos_pi_sub, h4]
  simp only [quantumCorr, aliceAngle, bobAngle]
  rw [show (0 : ℝ) - π / 4 = -(π / 4) by ring, Real.cos_neg, h4,
    show (0 : ℝ) - -(π / 4) = π / 4 by ring, h4,
    show π / 2 - π / 4 = π / 4 by ring, h4, h34]
  ring

/-- `2√2 > 2`: the quantum CHSH value exceeds the classical bound. -/
theorem two_sqrt_two_gt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]

/-- **Bell's theorem.** No local hidden-variable model reproduces the quantum-mechanical
correlations: there is no probability space of hidden variables together with local
`[-1,1]`-valued response functions `A i` for Alice and `B j` for Bob whose correlations
`∫ A i · B j` equal the quantum correlations `cos (αᵢ - βⱼ)` at the CHSH settings.

The proof is the CHSH inequality: any such model satisfies
`|E(A₁B₁) + E(A₁B₂) + E(A₂B₁) - E(A₂B₂)| ≤ 2`, while quantum mechanics predicts `2√2 > 2`. -/
theorem bell_theorem :
    ¬ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (A B : Bool → Ω → ℝ),
        (∀ i, Measurable (A i)) ∧ (∀ j, Measurable (B j)) ∧
        (∀ i ω, |A i ω| ≤ 1) ∧ (∀ j ω, |B j ω| ≤ 1) ∧
        (∀ i j, lhvCorr μ (A i) (B j) = quantumCorr i j) := by
  rintro ⟨Ω, _, μ, hμ, A, B, hA, hB, bA, bB, hcorr⟩
  have key := chsh_classical μ (A false) (A true) (B false) (B true)
    (hA false) (hA true) (hB false) (hB true) (bA false) (bA true) (bB false) (bB true)
  rw [hcorr false false, hcorr false true, hcorr true false, hcorr true true,
    quantum_chsh_value] at key
  have h2 := two_sqrt_two_gt_two
  have : (2 : ℝ) * Real.sqrt 2 ≤ 2 := le_trans (le_abs_self _) key
  linarith

/-- The class of local hidden-variable models in `bell_theorem` is non-empty: for instance the
deterministic model with all outcomes equal to `+1`, which produces all correlations equal to `1`.
So `bell_theorem` is not vacuous. -/
theorem lhv_model_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (A B : Bool → Ω → ℝ),
        (∀ i, Measurable (A i)) ∧ (∀ j, Measurable (B j)) ∧
        (∀ i ω, |A i ω| ≤ 1) ∧ (∀ j ω, |B j ω| ≤ 1) ∧
        (∀ i j, lhvCorr μ (A i) (B j) = 1) := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ _ => 1, fun _ _ => 1,
    fun _ => measurable_const, fun _ => measurable_const, fun _ _ => by norm_num,
    fun _ _ => by norm_num, fun i j => ?_⟩
  simp [lhvCorr]

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

