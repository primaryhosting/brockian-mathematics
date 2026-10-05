/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is given as a plain block comment and repeated verbatim below.)

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

/-- A local hidden-variable (LHV) model for a bipartite experiment with two binary
measurement settings per side.

`Ω` is the space of hidden variables, `μ` a probability distribution on it, and
`A i` (resp. `B j`) the deterministic response of Alice (resp. Bob) to setting `i`
(resp. `j`), a measurable function of the hidden variable alone (this is locality:
Alice's outcome does not depend on Bob's setting and conversely), taking values in
`[-1, 1]`. -/
structure LHVModel (Ω : Type*) [MeasurableSpace Ω] where
  /-- the distribution of the hidden variable -/
  μ : Measure Ω
  /-- `μ` is a probability measure -/
  isProb : IsProbabilityMeasure μ
  /-- Alice's response function for each of her two settings -/
  A : Bool → Ω → ℝ
  /-- Bob's response function for each of his two settings -/
  B : Bool → Ω → ℝ
  hA_meas : ∀ i, Measurable (A i)
  hB_meas : ∀ j, Measurable (B j)
  hA_bdd : ∀ i ω, |A i ω| ≤ 1
  hB_bdd : ∀ j ω, |B j ω| ≤ 1

namespace LHVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : LHVModel Ω)

attribute [instance] LHVModel.isProb

/-- The correlation predicted by the model when Alice uses setting `i` and Bob setting `j`. -/
noncomputable def corr (i j : Bool) : ℝ := ∫ ω, M.A i ω * M.B j ω ∂M.μ

/-- The CHSH combination of the four correlations of a local hidden-variable model. -/
noncomputable def chsh : ℝ :=
  M.corr false false + M.corr false true + M.corr true false - M.corr true true

lemma integrable_mul (i j : Bool) : Integrable (fun ω => M.A i ω * M.B j ω) M.μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((M.hA_meas i).mul (M.hB_meas j)).aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
  intro ω
  have : |M.A i ω * M.B j ω| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (M.hA_bdd i ω) (abs_nonneg _) (M.hB_bdd j ω)
  simpa [Real.norm_eq_abs] using this

/-- The CHSH combination is the integral of a single pointwise expression. -/
lemma chsh_eq_integral :
    M.chsh = ∫ ω, (M.A false ω * M.B false ω + M.A false ω * M.B true ω
      + M.A true ω * M.B false ω - M.A true ω * M.B true ω) ∂M.μ := by
  have h1 := integral_add (M.integrable_mul false false) (M.integrable_mul false true)
  have h2 := integral_add ((M.integrable_mul false false).add (M.integrable_mul false true))
    (M.integrable_mul true false)
  have h3 := integral_sub (((M.integrable_mul false false).add (M.integrable_mul false true)).add
    (M.integrable_mul true false)) (M.integrable_mul true true)
  simp only [Pi.add_apply] at h1 h2 h3
  rw [chsh, corr, corr, corr, corr, h3, h2, h1]

end LHVModel

/-- Pointwise CHSH bound: for numbers in `[-1,1]`, the CHSH expression is at most `2`
in absolute value. -/
lemma chsh_pointwise_bound {a0 a1 b0 b1 : ℝ} (ha0 : |a0| ≤ 1) (ha1 : |a1| ≤ 1)
    (hb0 : |b0| ≤ 1) (hb1 : |b1| ≤ 1) : |a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1| ≤ 2 := by
  have h1 : a0 * (b0 + b1) ≤ |b0 + b1| :=
    le_trans (le_abs_self _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha0)
  have h2 : a1 * (b0 - b1) ≤ |b0 - b1| :=
    le_trans (le_abs_self _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha1)
  have h1' : -(a0 * (b0 + b1)) ≤ |b0 + b1| :=
    le_trans (neg_le_abs _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha0)
  have h2' : -(a1 * (b0 - b1)) ≤ |b0 - b1| :=
    le_trans (neg_le_abs _)
      (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha1)
  have key : |b0 + b1| + |b0 - b1| ≤ 2 := by
    rcases abs_cases (b0 + b1) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (b0 - b1) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [e1, e2] <;> rw [abs_le] at hb0 hb1 <;> linarith [hb0.1, hb0.2, hb1.1, hb1.2]
  rw [abs_le]
  constructor <;> nlinarith

/-- **Bell/CHSH inequality**: every local hidden-variable model satisfies `|CHSH| ≤ 2`. -/
theorem chsh_le_two {Ω : Type*} [MeasurableSpace Ω] (M : LHVModel Ω) : |M.chsh| ≤ 2 := by
  haveI := M.isProb
  rw [M.chsh_eq_integral]
  have h : ‖∫ ω, (M.A false ω * M.B false ω + M.A false ω * M.B true ω
      + M.A true ω * M.B false ω - M.A true ω * M.B true ω) ∂M.μ‖ ≤ 2 * M.μ.real Set.univ := by
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω => ?_)
    simpa [Real.norm_eq_abs] using
      chsh_pointwise_bound (M.hA_bdd false ω) (M.hA_bdd true ω)
        (M.hB_bdd false ω) (M.hB_bdd true ω)
  simpa [Real.norm_eq_abs, probReal_univ] using h

/-- A concrete local hidden-variable model: a single hidden variable and both parties
always answering `+1`. -/
noncomputable def trivialLHVModel : LHVModel Unit where
  μ := Measure.dirac ()
  isProb := by infer_instance
  A := fun _ _ => 1
  B := fun _ _ => 1
  hA_meas := fun _ => measurable_const
  hB_meas := fun _ => measurable_const
  hA_bdd := by intro i ω; norm_num
  hB_bdd := by intro j ω; norm_num

/-- Local hidden-variable models exist, and the classical bound `2` is attained:
the bound of `Frontier.chsh_le_two` is sharp. -/
lemma chsh_le_two_sharp : |trivialLHVModel.chsh| = 2 := by
  have hc : ∀ i j : Bool, trivialLHVModel.corr i j = 1 := by
    intro i j
    simp [LHVModel.corr, trivialLHVModel]
  rw [LHVModel.chsh, hc, hc, hc, hc]
  norm_num

/-- The quantum-mechanical correlation of the spin singlet state for detector angles
`a` and `b`: `E(a,b) = -cos (a - b)`. -/
noncomputable def qcorr (a b : ℝ) : ℝ := -Real.cos (a - b)

/-- Alice's two detector angles in the standard CHSH configuration. -/
noncomputable def aliceAngle : Bool → ℝ
  | false => 0
  | true => Real.pi / 2

/-- Bob's two detector angles in the standard CHSH configuration. -/
noncomputable def bobAngle : Bool → ℝ
  | false => Real.pi / 4
  | true => -(Real.pi / 4)

/-- At the standard angles, the quantum CHSH value has absolute value `2√2`. -/
lemma quantum_chsh_value :
    |qcorr (aliceAngle false) (bobAngle false) + qcorr (aliceAngle false) (bobAngle true)
      + qcorr (aliceAngle true) (bobAngle false) - qcorr (aliceAngle true) (bobAngle true)|
      = 2 * Real.sqrt 2 := by
  have hpi : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  have hcos4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.pi / 2 - -(Real.pi / 4) = Real.pi - Real.pi / 4 := by ring
  have hcos34 : Real.cos (Real.pi - Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [Real.cos_pi_sub, hcos4]
  have hs : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  simp only [qcorr, aliceAngle, bobAngle, zero_sub, sub_neg_eq_add, zero_add,
    Real.cos_neg, hpi, h34, hcos4, hcos34]
  rw [abs_of_nonpos (by nlinarith)]
  ring

/-- `2√2 > 2`: the quantum CHSH value exceeds the classical bound. -/
lemma two_sqrt_two_gt_two : (2:ℝ) < 2 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]

/-- **Bell's theorem.**

1. (CHSH inequality) Every local hidden-variable model — a probability space of hidden
   variables together with `[-1,1]`-valued response functions depending only on the
   local setting and the hidden variable — satisfies `|CHSH| ≤ 2`.
2. (Quantum violation) The singlet correlations `E(a,b) = -cos (a - b)` of quantum
   mechanics give `|CHSH| = 2√2 > 2` at the standard detector angles.
3. Consequently no local hidden-variable model reproduces the quantum correlations:
   for every LHV model there is a pair of settings whose predicted correlation differs
   from the quantum-mechanical one. -/
theorem bell_theorem :
    (∀ {Ω : Type} [MeasurableSpace Ω] (M : LHVModel Ω), |M.chsh| ≤ 2) ∧
    (|qcorr (aliceAngle false) (bobAngle false) + qcorr (aliceAngle false) (bobAngle true)
      + qcorr (aliceAngle true) (bobAngle false) - qcorr (aliceAngle true) (bobAngle true)|
      = 2 * Real.sqrt 2 ∧ (2:ℝ) < 2 * Real.sqrt 2) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (M : LHVModel Ω),
      ∃ i j : Bool, M.corr i j ≠ qcorr (aliceAngle i) (bobAngle j)) := by
  refine ⟨fun {Ω} _ M => chsh_le_two M, ⟨quantum_chsh_value, two_sqrt_two_gt_two⟩, ?_⟩
  intro Ω _ M
  by_contra hcon
  push_neg at hcon
  have h : |M.chsh| = 2 * Real.sqrt 2 := by
    rw [LHVModel.chsh, hcon false false, hcon false true, hcon true false, hcon true true]
    exact quantum_chsh_value
  have := chsh_le_two M
  rw [h] at this
  linarith [two_sqrt_two_gt_two]

end Frontier

#print axioms Frontier.bell_theorem
#print axioms Frontier.chsh_le_two_sharp

