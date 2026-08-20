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

open scoped Real
open MeasureTheory Matrix

namespace Frontier

/-! ## The classical (local hidden variable) side -/

/-- The pointwise CHSH bound: if four numbers `a₀, a₁, b₀, b₁` have absolute value at most `1`
(the possible outcomes, or local averages of outcomes, of `±1`-valued measurements), then the
CHSH combination is bounded by `2` in absolute value. -/
theorem abs_chsh_pointwise_le_two {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1)
    (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2 := by
  rw [abs_le] at ha₀ ha₁ hb₀ hb₁ ⊢
  constructor <;>
  · rcases le_total 0 (b₀ + b₁) with hp | hp <;> rcases le_total 0 (b₀ - b₁) with hq | hq <;>
      nlinarith [ha₀.1, ha₀.2, ha₁.1, ha₁.2, hb₀.1, hb₀.2, hb₁.1, hb₁.2]

/-- A **local hidden variable model** for a bipartite experiment with two binary measurement
settings per side: a probability space of hidden variables `Ω`, together with response functions
`a i ω` (Alice, setting `i`) and `b j ω` (Bob, setting `j`) taking values in `[-1, 1]`.  The
crucial locality assumption is built into the shape of the data: Alice's response depends only on
her own setting `i` and on the shared hidden variable `ω` (and likewise for Bob). -/
structure LHVModel where
  /-- The space of hidden variables. -/
  Ω : Type
  /-- Measurable structure on the hidden variable space. -/
  measurable : MeasurableSpace Ω
  /-- The distribution of the hidden variable. -/
  μ : Measure Ω
  /-- The hidden variable is distributed according to a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- Alice's local response function for each of her two settings. -/
  a : Fin 2 → Ω → ℝ
  /-- Bob's local response function for each of his two settings. -/
  b : Fin 2 → Ω → ℝ
  /-- Alice's responses take values in `[-1, 1]`. -/
  ha : ∀ i ω, |a i ω| ≤ 1
  /-- Bob's responses take values in `[-1, 1]`. -/
  hb : ∀ j ω, |b j ω| ≤ 1
  /-- The correlation functions are integrable. -/
  hint : ∀ i j, Integrable (fun ω => a i ω * b j ω) μ

attribute [instance] LHVModel.measurable LHVModel.prob

/-- The correlation predicted by a local hidden variable model for settings `(i, j)`. -/
noncomputable def LHVModel.corr (M : LHVModel) (i j : Fin 2) : ℝ :=
  ∫ ω, M.a i ω * M.b j ω ∂M.μ

/-- **CHSH inequality for local hidden variable models.**  Every local hidden variable model
satisfies `|E(0,0) + E(0,1) + E(1,0) - E(1,1)| ≤ 2`. -/
theorem LHVModel.abs_chsh_le_two (M : LHVModel) :
    |M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1| ≤ 2 := by
  have hsum : M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1 =
      ∫ ω, (M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω
        - M.a 1 ω * M.b 1 ω) ∂M.μ := by
    have i01 : Integrable (fun ω => M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω) M.μ := by
      simpa using (M.hint 0 0).add (M.hint 0 1)
    have i012 : Integrable
        (fun ω => M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω) M.μ := by
      simpa using i01.add (M.hint 1 0)
    simp only [LHVModel.corr]
    rw [← integral_add (M.hint 0 0) (M.hint 0 1), ← integral_add i01 (M.hint 1 0),
      ← integral_sub i012 (M.hint 1 1)]
  have hInt : Integrable (fun ω => M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω
      - M.a 1 ω * M.b 1 ω) M.μ :=
    (((M.hint 0 0).add (M.hint 0 1)).add (M.hint 1 0)).sub (M.hint 1 1)
  rw [hsum]
  refine (abs_integral_le_integral_abs).trans ?_
  have hmono : ∫ ω, |M.a 0 ω * M.b 0 ω + M.a 0 ω * M.b 1 ω + M.a 1 ω * M.b 0 ω
      - M.a 1 ω * M.b 1 ω| ∂M.μ ≤ ∫ _ω, (2 : ℝ) ∂M.μ := by
    refine integral_mono hInt.abs (integrable_const 2) fun ω => ?_
    exact abs_chsh_pointwise_le_two (M.ha 0 ω) (M.ha 1 ω) (M.hb 0 ω) (M.hb 1 ω)
  simpa using hmono

/-! ## The quantum side: an explicit two-qubit model violating the CHSH bound -/

/-- `s = 1/√2`. -/
noncomputable def s : ℝ := (Real.sqrt 2)⁻¹

theorem s_sq : s * s = 1 / 2 := by
  rw [s, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Local hidden variable models exist: the deterministic model where both parties always
answer `+1`.  This shows the statements about local hidden variable models are not vacuous. -/
noncomputable def constLHV : LHVModel where
  Ω := Unit
  measurable := inferInstance
  μ := Measure.dirac ()
  prob := inferInstance
  a := fun _ _ => 1
  b := fun _ _ => 1
  ha := by simp
  hb := by simp
  hint := fun _ _ => by
    have : IsProbabilityMeasure (Measure.dirac (α := Unit) ()) := inferInstance
    simp using integrable_const (μ := Measure.dirac (α := Unit) ()) (1 : ℝ)

/-- The classical CHSH bound `2` is attained, so the inequality of `LHVModel.abs_chsh_le_two`
is sharp. -/
theorem constLHV_chsh :
    constLHV.corr 0 0 + constLHV.corr 0 1 + constLHV.corr 1 0 - constLHV.corr 1 1 = 2 := by
  have h : ∀ i j, constLHV.corr i j = 1 := by
    intro i j
    simp [LHVModel.corr, constLHV]
  rw [h, h, h, h]
  norm_num

/-- Alice's observables: `Z ⊗ I` and `X ⊗ I` on two qubits (real `4 × 4` matrices). -/
noncomputable def qA : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ
  | 0 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
  | 1 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

/-- Bob's observables: `I ⊗ (Z + X)/√2` and `I ⊗ (Z - X)/√2`. -/
noncomputable def qB : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ
  | 0 => !![s, s, 0, 0; s, -s, 0, 0; 0, 0, s, s; 0, 0, s, -s]
  | 1 => !![s, -s, 0, 0; -s, -s, 0, 0; 0, 0, s, -s; 0, 0, -s, -s]

/-- The maximally entangled state `(|00⟩ + |11⟩)/√2`. -/
noncomputable def qPsi : Fin 4 → ℝ := ![s, 0, 0, s]

/-- The quantum correlation `⟪ψ, Aᵢ Bⱼ ψ⟫`. -/
noncomputable def qCorr (i j : Fin 2) : ℝ := qPsi ⬝ᵥ ((qA i * qB j) *ᵥ qPsi)

theorem qPsi_unit : qPsi ⬝ᵥ qPsi = 1 := by
  simp [qPsi, dotProduct, Fin.sum_univ_four]
  linear_combination 2 * s_sq

theorem qA_symm (i : Fin 2) : (qA i)ᵀ = qA i := by
  fin_cases i <;> (ext p q; fin_cases p <;> fin_cases q <;> simp [qA])

theorem qB_symm (j : Fin 2) : (qB j)ᵀ = qB j := by
  fin_cases j <;> (ext p q; fin_cases p <;> fin_cases q <;> simp [qB])

theorem qA_sq (i : Fin 2) : qA i * qA i = 1 := by
  fin_cases i <;>
    (ext p q; fin_cases p <;> fin_cases q <;>
      simp [qA, Matrix.mul_apply, Fin.sum_univ_four])

theorem qB_sq (j : Fin 2) : qB j * qB j = 1 := by
  fin_cases j <;>
    (ext p q; fin_cases p <;> fin_cases q <;>
      simp [qB, Matrix.mul_apply, Fin.sum_univ_four] <;> nlinarith [s_sq])

theorem qA_qB_commute (i j : Fin 2) : qA i * qB j = qB j * qA i := by
  fin_cases i <;> fin_cases j <;>
    (ext p q; fin_cases p <;> fin_cases q <;>
      simp [qA, qB, Matrix.mul_apply, Fin.sum_univ_four])

theorem qCorr_eq (i j : Fin 2) :
    qCorr i j = if i = 1 ∧ j = 1 then -s else s := by
  fin_cases i <;> fin_cases j <;>
    · simp [qCorr, qA, qB, qPsi, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
      first
        | linear_combination (2 * s) * s_sq
        | linear_combination (-2 * s) * s_sq

/-- The quantum CHSH value is `2√2`, exceeding the classical bound `2`. -/
theorem qCorr_chsh : qCorr 0 0 + qCorr 0 1 + qCorr 1 0 - qCorr 1 1 = 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp only [qCorr_eq]
  norm_num [s]
  field_simp
  linarith [h2]

/-- **Bell's theorem.**  There is a quantum model (two spin-`1/2` particles in a maximally
entangled state, with two `±1`-valued spin observables on each side, Alice's commuting with
Bob's) whose correlations `qCorr` achieve the CHSH value `2√2`; and *no* local hidden variable
model reproduces these correlations, since every local hidden variable model obeys the CHSH
bound `|E(0,0) + E(0,1) + E(1,0) - E(1,1)| ≤ 2 < 2√2`. -/
theorem bell_theorem :
    -- the quantum observables are self-adjoint, `±1`-valued, and Alice's commute with Bob's,
    (∀ i, (qA i)ᵀ = qA i) ∧ (∀ j, (qB j)ᵀ = qB j) ∧
    (∀ i, qA i * qA i = 1) ∧ (∀ j, qB j * qB j = 1) ∧
    (∀ i j, qA i * qB j = qB j * qA i) ∧
    -- the state is a unit vector, and the quantum CHSH value is `2√2 > 2`,
    qPsi ⬝ᵥ qPsi = 1 ∧
    qCorr 0 0 + qCorr 0 1 + qCorr 1 0 - qCorr 1 1 = 2 * Real.sqrt 2 ∧
    2 < 2 * Real.sqrt 2 ∧
    -- every local hidden variable model obeys the CHSH bound,
    (∀ M : LHVModel, |M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1| ≤ 2) ∧
    -- and hence no local hidden variable model reproduces the quantum correlations.
    ¬ ∃ M : LHVModel, ∀ i j, M.corr i j = qCorr i j := by
  have hgt : (2 : ℝ) < 2 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2,
      Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2), Real.sqrt_one]
  refine ⟨qA_symm, qB_symm, qA_sq, qB_sq, qA_qB_commute, qPsi_unit, qCorr_chsh, hgt,
    fun M => M.abs_chsh_le_two, ?_⟩
  rintro ⟨M, hM⟩
  have h := M.abs_chsh_le_two
  rw [hM 0 0, hM 0 1, hM 1 0, hM 1 1, qCorr_chsh] at h
  rw [abs_of_nonneg (by positivity)] at h
  linarith

/-!
## Relation to the existing Mathlib material

Mathlib contains a purely algebraic counterpart of the classical bound,
`CHSH_inequality_of_comm` (in `Mathlib/Algebra/Star/CHSH.lean`): in a *commutative* ordered
`*`-algebra over `ℝ`, a CHSH tuple satisfies `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁ ≤ 2`; and
`tsirelson_inequality`, giving the bound `2^(3/2)` in the noncommutative case.  It does not,
however, contain the probabilistic (local hidden variable) formulation, nor an explicit quantum
model violating the classical bound, which is what is proved above.  As a consistency check, our
quantum observables do form a CHSH tuple in the sense of Mathlib. -/
theorem qIsCHSHTuple : IsCHSHTuple (qA 0) (qA 1) (qB 0) (qB 1) where
  A₀_inv := by rw [sq]; exact qA_sq 0
  A₁_inv := by rw [sq]; exact qA_sq 1
  B₀_inv := by rw [sq]; exact qB_sq 0
  B₁_inv := by rw [sq]; exact qB_sq 1
  A₀_sa := qA_symm 0
  A₁_sa := qA_symm 1
  B₀_sa := qB_symm 0
  B₁_sa := qB_symm 1
  A₀B₀_commutes := qA_qB_commute 0 0
  A₀B₁_commutes := qA_qB_commute 0 1
  A₁B₀_commutes := qA_qB_commute 1 0
  A₁B₁_commutes := qA_qB_commute 1 1

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

