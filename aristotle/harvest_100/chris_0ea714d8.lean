import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-! ## Local hidden-variable models

A local hidden-variable (LHV) model for a bipartite experiment with two measurement
settings per side consists of:

* a probability space `(Λ, μ)` of hidden variables;
* for each of Alice's two settings `i : Bool`, a response function `A i : Λ → ℝ`
  taking values in `[-1, 1]`, depending only on Alice's setting and the hidden variable
  (this is the locality/no-signalling assumption: `A i λ` does not depend on Bob's
  setting `j`, and symmetrically for `B`);
* likewise for Bob, `B j : Λ → ℝ` with values in `[-1, 1]`.

The measured correlation for settings `(i, j)` is `∫ λ, A i λ * B j λ ∂μ`.
-/

/-- `IsLHV μ A B` says that `(μ, A, B)` is a local hidden-variable model:
`μ` is a probability measure on the hidden variables, the response functions are
measurable, and they take values in `[-1, 1]`. -/
structure IsLHV {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A B : Bool → Λ → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measA : ∀ i : Bool, AEStronglyMeasurable (A i) μ
  measB : ∀ j : Bool, AEStronglyMeasurable (B j) μ
  boundA : ∀ (i : Bool) (l : Λ), |A i l| ≤ 1
  boundB : ∀ (j : Bool) (l : Λ), |B j l| ≤ 1

/-- The correlation predicted by a local hidden-variable model for settings `(i, j)`. -/
noncomputable def lhvCorr {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A B : Bool → Λ → ℝ) (i j : Bool) : ℝ :=
  ∫ l, A i l * B j l ∂μ

/-- The CHSH combination of the four correlations of a local hidden-variable model. -/
noncomputable def lhvCHSH {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A B : Bool → Λ → ℝ) : ℝ :=
  lhvCorr μ A B false false + lhvCorr μ A B false true
    + lhvCorr μ A B true false - lhvCorr μ A B true true

/-! ## Quantum correlations for the singlet state

For a maximally entangled two-qubit state measured along directions at angles
`x` (Alice) and `y` (Bob) in a fixed plane, quantum mechanics predicts the
correlation `cos (x - y)` (up to the overall sign convention fixed by the state).
The Tsirelson settings below are Alice `0, π/2` and Bob `π/4, -π/4`. -/

/-- Alice's two measurement angles at the Tsirelson settings. -/
noncomputable def aliceAngle : Bool → ℝ
  | false => 0
  | true => Real.pi / 2

/-- Bob's two measurement angles at the Tsirelson settings. -/
noncomputable def bobAngle : Bool → ℝ
  | false => Real.pi / 4
  | true => -(Real.pi / 4)

/-- The quantum-mechanical correlation for settings `(i, j)` at the Tsirelson angles. -/
noncomputable def quantumCorr (i j : Bool) : ℝ :=
  Real.cos (aliceAngle i - bobAngle j)

/-! ## The classical (CHSH) bound -/

/-- The pointwise CHSH inequality: for reals in `[-1,1]`,
`a₀b₀ + a₀b₁ + a₁b₀ - a₁b₁` has absolute value at most `2`.

(Compare `CHSH_inequality_of_comm` in Mathlib, which gives the one-sided bound in any
commutative ordered `*`-algebra for a dichotomic CHSH tuple; here we need the two-sided
bound for arbitrary values in `[-1,1]`, so we prove it directly.) -/
theorem abs_chsh_pointwise_le_two {a₀ a₁ b₀ b₁ : ℝ}
    (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2 := by
  rw [abs_le] at ha₀ ha₁ hb₀ hb₁
  obtain ⟨ha₀l, ha₀u⟩ := ha₀
  obtain ⟨ha₁l, ha₁u⟩ := ha₁
  obtain ⟨hb₀l, hb₀u⟩ := hb₀
  obtain ⟨hb₁l, hb₁u⟩ := hb₁
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 ha₀u) (sub_nonneg.2 hb₀u),
      mul_nonneg (sub_nonneg.2 ha₀u) (sub_nonneg.2 hb₁u),
      mul_nonneg (sub_nonneg.2 ha₁u) (sub_nonneg.2 hb₀u),
      mul_nonneg (sub_nonneg.2 ha₁u) (sub_nonneg.2 hb₁u),
      mul_nonneg (sub_nonneg.2 ha₀l) (sub_nonneg.2 hb₀l),
      mul_nonneg (sub_nonneg.2 ha₀l) (sub_nonneg.2 hb₁l),
      mul_nonneg (sub_nonneg.2 ha₁l) (sub_nonneg.2 hb₀l),
      mul_nonneg (sub_nonneg.2 ha₁l) (sub_nonneg.2 hb₁l),
      mul_nonneg (sub_nonneg.2 ha₀u) (sub_nonneg.2 hb₀l),
      mul_nonneg (sub_nonneg.2 ha₀l) (sub_nonneg.2 hb₀u),
      mul_nonneg (sub_nonneg.2 ha₁u) (sub_nonneg.2 hb₁l),
      mul_nonneg (sub_nonneg.2 ha₁l) (sub_nonneg.2 hb₁u)]
  · nlinarith [mul_nonneg (sub_nonneg.2 ha₀u) (sub_nonneg.2 hb₀u),
      mul_nonneg (sub_nonneg.2 ha₀u) (sub_nonneg.2 hb₁u),
      mul_nonneg (sub_nonneg.2 ha₁u) (sub_nonneg.2 hb₀u),
      mul_nonneg (sub_nonneg.2 ha₁u) (sub_nonneg.2 hb₁u),
      mul_nonneg (sub_nonneg.2 ha₀l) (sub_nonneg.2 hb₀l),
      mul_nonneg (sub_nonneg.2 ha₀l) (sub_nonneg.2 hb₁l),
      mul_nonneg (sub_nonneg.2 ha₁l) (sub_nonneg.2 hb₀l),
      mul_nonneg (sub_nonneg.2 ha₁l) (sub_nonneg.2 hb₁l),
      mul_nonneg (sub_nonneg.2 ha₀u) (sub_nonneg.2 hb₀l),
      mul_nonneg (sub_nonneg.2 ha₀l) (sub_nonneg.2 hb₀u),
      mul_nonneg (sub_nonneg.2 ha₁u) (sub_nonneg.2 hb₁l),
      mul_nonneg (sub_nonneg.2 ha₁l) (sub_nonneg.2 hb₁u)]

/-- Each product `A i * B j` of response functions of an LHV model is integrable. -/
theorem IsLHV.integrable_mul {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ}
    {A B : Bool → Λ → ℝ} (h : IsLHV μ A B) (i j : Bool) :
    Integrable (fun l => A i l * B j l) μ := by
  haveI := h.isProbabilityMeasure
  refine Integrable.of_bound (((h.measA i).mul (h.measB j))) 1 ?_
  filter_upwards with l
  have h1 : |A i l| ≤ 1 := h.boundA i l
  have h2 : |B j l| ≤ 1 := h.boundB j l
  rw [Real.norm_eq_abs, abs_mul]
  calc |A i l| * |B j l| ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := by ring

/-- **Classical CHSH bound.** Every local hidden-variable model satisfies `|CHSH| ≤ 2`. -/
theorem lhv_abs_chsh_le_two {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ}
    {A B : Bool → Λ → ℝ} (h : IsLHV μ A B) :
    |lhvCHSH μ A B| ≤ 2 := by
  haveI := h.isProbabilityMeasure
  have i1 : Integrable (fun l => A false l * B false l) μ := h.integrable_mul false false
  have i2 : Integrable (fun l => A false l * B true l) μ := h.integrable_mul false true
  have i3 : Integrable (fun l => A true l * B false l) μ := h.integrable_mul true false
  have i4 : Integrable (fun l => A true l * B true l) μ := h.integrable_mul true true
  have i12 : Integrable (fun l => A false l * B false l + A false l * B true l) μ := i1.add i2
  have i123 : Integrable
      (fun l => A false l * B false l + A false l * B true l + A true l * B false l) μ :=
    i12.add i3
  have hsum : lhvCHSH μ A B
      = ∫ l, (A false l * B false l + A false l * B true l
          + A true l * B false l - A true l * B true l) ∂μ := by
    rw [integral_sub i123 i4, integral_add i12 i3, integral_add i1 i2]
    rfl
  rw [hsum]
  have hbound : ‖∫ l, (A false l * B false l + A false l * B true l
      + A true l * B false l - A true l * B true l) ∂μ‖ ≤ 2 * μ.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards with l
    rw [Real.norm_eq_abs]
    exact abs_chsh_pointwise_le_two (h.boundA false l) (h.boundA true l)
      (h.boundB false l) (h.boundB true l)
  simpa [Real.norm_eq_abs, probReal_univ] using hbound

/-- Sanity check: local hidden-variable models exist (so the notion is not vacuous).
The trivial model on a one-point space with all responses equal to `1` is one. -/
theorem exists_isLHV :
    IsLHV (Measure.dirac () : Measure Unit) (fun _ _ => 1) (fun _ _ => 1) where
  isProbabilityMeasure := by infer_instance
  measA := fun _ => aestronglyMeasurable_const
  measB := fun _ => aestronglyMeasurable_const
  boundA := by simp
  boundB := by simp

/-! ## Quantum violation -/

/-- At the Tsirelson settings the quantum CHSH value is `2√2`. -/
theorem quantum_chsh_eq :
    quantumCorr false false + quantumCorr false true
      + quantumCorr true false - quantumCorr true true = 2 * Real.sqrt 2 := by
  have h1 : quantumCorr false false = Real.sqrt 2 / 2 := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show (0 : ℝ) - Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg,
      Real.cos_pi_div_four]
  have h2 : quantumCorr false true = Real.sqrt 2 / 2 := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show (0 : ℝ) - -(Real.pi / 4) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have h3 : quantumCorr true false = Real.sqrt 2 / 2 := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have h4 : quantumCorr true true = -(Real.sqrt 2 / 2) := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show Real.pi / 2 - -(Real.pi / 4) = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
  rw [h1, h2, h3, h4]
  ring

/-- `2 * √2 > 2`. -/
theorem two_lt_two_mul_sqrt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

/-! ## Bell's theorem -/

/-- **Bell's theorem.**

1. (CHSH inequality) Every local hidden-variable model — a probability space of hidden
   variables together with `[-1,1]`-valued response functions depending only on the local
   setting and the hidden variable — satisfies `|CHSH| ≤ 2`.
2. (Quantum violation) The quantum-mechanical correlations of a maximally entangled pair
   at the Tsirelson settings have CHSH value `2√2 > 2`.
3. Consequently, no local hidden-variable model reproduces the quantum correlations. -/
theorem bell_theorem :
    (∀ {Λ : Type} [MeasurableSpace Λ] (μ : Measure Λ) (A B : Bool → Λ → ℝ),
        IsLHV μ A B → |lhvCHSH μ A B| ≤ 2) ∧
    (quantumCorr false false + quantumCorr false true
      + quantumCorr true false - quantumCorr true true = 2 * Real.sqrt 2 ∧
      (2 : ℝ) < 2 * Real.sqrt 2) ∧
    ¬ ∃ (Λ : Type) (_ : MeasurableSpace Λ) (μ : Measure Λ) (A B : Bool → Λ → ℝ),
        IsLHV μ A B ∧ ∀ i j : Bool, lhvCorr μ A B i j = quantumCorr i j := by
  refine ⟨fun {Λ} _ μ A B h => lhv_abs_chsh_le_two h,
    ⟨quantum_chsh_eq, two_lt_two_mul_sqrt_two⟩, ?_⟩
  rintro ⟨Λ, _, μ, A, B, h, hq⟩
  have hbound : |lhvCHSH μ A B| ≤ 2 := lhv_abs_chsh_le_two h
  have heq : lhvCHSH μ A B = 2 * Real.sqrt 2 := by
    rw [lhvCHSH, hq, hq, hq, hq]
    exact quantum_chsh_eq
  rw [heq] at hbound
  have := abs_le.1 hbound
  linarith [two_lt_two_mul_sqrt_two, this.2]

end Frontier

