/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-- A local hidden-variable (LHV) model for a bipartite experiment with two measurement
settings per side.  A hidden variable `l : Λ` is drawn from a probability distribution `μ`;
Alice's outcome for setting `i` is `A i l` and Bob's outcome for setting `j` is `B j l`.
Locality is expressed by the fact that `A i l` does not depend on Bob's setting `j`
and `B j l` does not depend on Alice's setting `i`.  Outcomes take values in `[-1, 1]`
(this includes the usual `±1`-valued outcomes). -/
structure LHVModel where
  /-- The space of hidden variables. -/
  Λ : Type*
  /-- Measurable structure on the hidden variables. -/
  measΛ : MeasurableSpace Λ
  /-- The distribution of the hidden variable. -/
  μ : Measure Λ
  /-- `μ` is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- Alice's outcome function, depending only on her setting and the hidden variable. -/
  A : Fin 2 → Λ → ℝ
  /-- Bob's outcome function, depending only on his setting and the hidden variable. -/
  B : Fin 2 → Λ → ℝ
  /-- Measurability of Alice's outcomes. -/
  A_meas : ∀ i, AEStronglyMeasurable (A i) μ
  /-- Measurability of Bob's outcomes. -/
  B_meas : ∀ j, AEStronglyMeasurable (B j) μ
  /-- Alice's outcomes lie in `[-1,1]`. -/
  A_bdd : ∀ i l, |A i l| ≤ 1
  /-- Bob's outcomes lie in `[-1,1]`. -/
  B_bdd : ∀ j l, |B j l| ≤ 1

attribute [instance] LHVModel.measΛ LHVModel.isProb

/-- The correlation predicted by a local hidden-variable model for settings `(i, j)`. -/
noncomputable def LHVModel.corr (M : LHVModel) (i j : Fin 2) : ℝ :=
  ∫ l, M.A i l * M.B j l ∂M.μ

/-- The CHSH combination of a correlation table. -/
def CHSH (E : Fin 2 → Fin 2 → ℝ) : ℝ := E 0 0 + E 0 1 + E 1 0 - E 1 1

/-- Pointwise CHSH bound for numbers in `[-1,1]`. -/
theorem abs_chsh_pointwise_le_two {a b c d : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) : |a * c + a * d + b * c - b * d| ≤ 2 := by
  rw [abs_le] at ha hb hc hd
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  obtain ⟨h5, h6⟩ := hc
  obtain ⟨h7, h8⟩ := hd
  have hA : ∀ x y : ℝ, -1 ≤ x → x ≤ 1 → -1 ≤ y → y ≤ 1 →
      (1 - x) * (1 - y) ≥ 0 ∧ (1 - x) * (1 + y) ≥ 0 ∧
      (1 + x) * (1 - y) ≥ 0 ∧ (1 + x) * (1 + y) ≥ 0 := by
    intro x y hx hx' hy hy'
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  obtain ⟨p1, p2, p3, p4⟩ := hA a c h1 h2 h5 h6
  obtain ⟨q1, q2, q3, q4⟩ := hA a d h1 h2 h7 h8
  obtain ⟨r1, r2, r3, r4⟩ := hA b c h3 h4 h5 h6
  obtain ⟨s1, s2, s3, s4⟩ := hA b d h3 h4 h7 h8
  rw [abs_le]
  constructor <;> rcases le_total c d with h | h <;>
    rcases le_total (c + d) 0 with h' | h' <;> nlinarith

/-- Products of outcome functions are integrable. -/
theorem LHVModel.integrable_prod (M : LHVModel) (i j : Fin 2) :
    Integrable (fun l => M.A i l * M.B j l) M.μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ((M.A_meas i).mul (M.B_meas j)) ?_
  filter_upwards with l
  rw [Real.norm_eq_abs, abs_mul]
  calc |M.A i l| * |M.B j l| ≤ 1 * 1 :=
        mul_le_mul (M.A_bdd i l) (M.B_bdd j l) (abs_nonneg _) zero_le_one
    _ = 1 := by ring

/-- **Bell/CHSH inequality**: every local hidden-variable model satisfies `|CHSH| ≤ 2`. -/
theorem LHVModel.abs_chsh_corr_le_two (M : LHVModel) : |CHSH M.corr| ≤ 2 := by
  have hint : ∀ i j : Fin 2, Integrable (fun l => M.A i l * M.B j l) M.μ := M.integrable_prod
  have hsum : CHSH M.corr =
      ∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l
              - M.A 1 l * M.B 1 l) ∂M.μ := by
    have h1 : M.corr 0 0 + M.corr 0 1
        = ∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l) ∂M.μ :=
      (integral_add (hint 0 0) (hint 0 1)).symm
    have h2 : (∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l) ∂M.μ) + M.corr 1 0
        = ∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l) ∂M.μ :=
      (integral_add ((hint 0 0).add (hint 0 1)) (hint 1 0)).symm
    have h3 : (∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l) ∂M.μ)
          - M.corr 1 1
        = ∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l
                  - M.A 1 l * M.B 1 l) ∂M.μ :=
      (integral_sub (((hint 0 0).add (hint 0 1)).add (hint 1 0)) (hint 1 1)).symm
    rw [CHSH, h1, h2, h3]
  rw [hsum]
  have hbound : ∀ l : M.Λ,
      |M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l - M.A 1 l * M.B 1 l| ≤ 2 :=
    fun l => abs_chsh_pointwise_le_two (M.A_bdd 0 l) (M.A_bdd 1 l) (M.B_bdd 0 l) (M.B_bdd 1 l)
  calc |∫ l, (M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l
              - M.A 1 l * M.B 1 l) ∂M.μ|
      ≤ ∫ l, |M.A 0 l * M.B 0 l + M.A 0 l * M.B 1 l + M.A 1 l * M.B 0 l
              - M.A 1 l * M.B 1 l| ∂M.μ := abs_integral_le_integral_abs
    _ ≤ ∫ _l : M.Λ, (2 : ℝ) ∂M.μ := by
        refine integral_mono ?_ (integrable_const _) hbound
        exact (((hint 0 0).add (hint 0 1)).add (hint 1 0)).sub (hint 1 1) |>.abs
    _ = 2 := by simp

/-- A trivial local hidden-variable model: a single hidden variable and all outcomes `+1`.
Its CHSH value is exactly `2`, so the classical bound is attained. -/
noncomputable def trivialModel : LHVModel.{0} where
  Λ := Unit
  measΛ := inferInstance
  μ := Measure.dirac ()
  isProb := by infer_instance
  A := fun _ _ => 1
  B := fun _ _ => 1
  A_meas := fun _ => aestronglyMeasurable_const
  B_meas := fun _ => aestronglyMeasurable_const
  A_bdd := fun _ _ => by norm_num
  B_bdd := fun _ _ => by norm_num

/-- The classical bound is attained: there is a local hidden-variable model whose CHSH value
is exactly `2`.  (In particular the notion of an LHV model is not vacuous.) -/
theorem exists_lhvModel_chsh_eq_two : ∃ M : LHVModel.{0}, CHSH M.corr = 2 := by
  refine ⟨trivialModel, ?_⟩
  have h : ∀ i j : Fin 2, trivialModel.corr i j = 1 := by
    intro i j
    simp [LHVModel.corr, trivialModel]
  rw [CHSH, h, h, h, h]
  norm_num

/-- Alice's two measurement angles in the quantum (singlet) experiment. -/
noncomputable def angleA : Fin 2 → ℝ := ![0, π / 2]

/-- Bob's two measurement angles in the quantum (singlet) experiment. -/
noncomputable def angleB : Fin 2 → ℝ := ![π / 4, -(π / 4)]

/-- The quantum-mechanical correlations of the spin singlet state for coplanar spin
measurements at the angles `angleA i` and `angleB j`: `E(i,j) = -cos(αᵢ - βⱼ)`. -/
noncomputable def quantumCorr (i j : Fin 2) : ℝ := -Real.cos (angleA i - angleB j)

/-- The quantum CHSH value at these angles has absolute value `2√2`. -/
theorem abs_chsh_quantumCorr : |CHSH quantumCorr| = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (π / 2 + π / 4) = -(Real.sqrt 2 / 2) := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_pi_div_four, h4]
    ring
  have e00 : quantumCorr 0 0 = -(Real.sqrt 2 / 2) := by
    simp [quantumCorr, angleA, angleB, Real.cos_neg, h4]
  have e01 : quantumCorr 0 1 = -(Real.sqrt 2 / 2) := by
    simp [quantumCorr, angleA, angleB, h4]
  have e10 : quantumCorr 1 0 = -(Real.sqrt 2 / 2) := by
    have : π / 2 - π / 4 = π / 4 := by ring
    simp [quantumCorr, angleA, angleB, this, h4]
  have e11 : quantumCorr 1 1 = Real.sqrt 2 / 2 := by
    have : π / 2 - -(π / 4) = π / 2 + π / 4 := by ring
    simp [quantumCorr, angleA, angleB, this, h34]
  have hs : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
  rw [CHSH, e00, e01, e10, e11]
  rw [abs_of_nonpos (by linarith)]
  ring

/-- `2√2 > 2`. -/
theorem two_lt_two_mul_sqrt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  linarith

/-- **Bell's theorem.**

1.  Every local hidden-variable model obeys the CHSH inequality `|CHSH| ≤ 2`.
2.  The quantum-mechanical correlations of the singlet state at the angles
    `angleA`, `angleB` give `|CHSH| = 2√2 > 2`.
3.  Consequently no local hidden-variable model reproduces the quantum correlations. -/
theorem bell_theorem :
    (∀ M : LHVModel, |CHSH M.corr| ≤ 2) ∧
    |CHSH quantumCorr| = 2 * Real.sqrt 2 ∧ 2 < |CHSH quantumCorr| ∧
    ¬ ∃ M : LHVModel, M.corr = quantumCorr := by
  refine ⟨fun M => M.abs_chsh_corr_le_two, abs_chsh_quantumCorr, ?_, ?_⟩
  · rw [abs_chsh_quantumCorr]; exact two_lt_two_mul_sqrt_two
  · rintro ⟨M, hM⟩
    have h1 : |CHSH M.corr| ≤ 2 := M.abs_chsh_corr_le_two
    rw [hM, abs_chsh_quantumCorr] at h1
    linarith [two_lt_two_mul_sqrt_two]

end Frontier

