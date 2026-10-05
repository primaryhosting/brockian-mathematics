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

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH inequality: for outcomes in `[-1, 1]`, the CHSH combination is
bounded by `2`. -/
theorem chsh_pointwise (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : |a₁| ≤ 1) (ha₂ : |a₂| ≤ 1) (hb₁ : |b₁| ≤ 1) (hb₂ : |b₂| ≤ 1) :
    |a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂| ≤ 2 := by
  have h1 : |a₁ * (b₁ + b₂)| ≤ |b₁ + b₂| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (b₁ + b₂)]
  have h2 : |a₂ * (b₁ - b₂)| ≤ |b₁ - b₂| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (b₁ - b₂)]
  have h3 : |b₁ + b₂| + |b₁ - b₂| ≤ 2 := by
    rcases abs_cases (b₁ + b₂) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (b₁ - b₂) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [abs_le] at hb₁ hb₂ <;> rw [e1, e2] <;> linarith [hb₁.1, hb₁.2, hb₂.1, hb₂.2]
  have key : a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ = a₁ * (b₁ + b₂) + a₂ * (b₁ - b₂) := by ring
  rw [key]
  calc |a₁ * (b₁ + b₂) + a₂ * (b₁ - b₂)| ≤ |a₁ * (b₁ + b₂)| + |a₂ * (b₁ - b₂)| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- A local hidden-variable model: a probability space of hidden variables `Ω` together with
deterministic (`[-1,1]`-valued) response functions for two measurement settings on each side. -/
structure LHVModel (Ω : Type) [MeasurableSpace Ω] where
  /-- The distribution of the hidden variable. -/
  μ : Measure Ω
  /-- The hidden variable distribution is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- Alice's response function for setting `1`. -/
  A₁ : Ω → ℝ
  /-- Alice's response function for setting `2`. -/
  A₂ : Ω → ℝ
  /-- Bob's response function for setting `1`. -/
  B₁ : Ω → ℝ
  /-- Bob's response function for setting `2`. -/
  B₂ : Ω → ℝ
  hA₁ : ∀ ω, |A₁ ω| ≤ 1
  hA₂ : ∀ ω, |A₂ ω| ≤ 1
  hB₁ : ∀ ω, |B₁ ω| ≤ 1
  hB₂ : ∀ ω, |B₂ ω| ≤ 1
  intAB : ∀ i j : Fin 2, Integrable
    (fun ω => (if i = 0 then A₁ ω else A₂ ω) * (if j = 0 then B₁ ω else B₂ ω)) μ

namespace LHVModel

variable {Ω : Type} [MeasurableSpace Ω]

/-- The correlation predicted by the model for settings `(i, j)`. -/
noncomputable def corr (M : LHVModel Ω) (i j : Fin 2) : ℝ :=
  ∫ ω, (if i = 0 then M.A₁ ω else M.A₂ ω) * (if j = 0 then M.B₁ ω else M.B₂ ω) ∂M.μ

/-- The CHSH combination of the four correlations of a local hidden-variable model. -/
noncomputable def chsh (M : LHVModel Ω) : ℝ :=
  M.corr 0 0 + M.corr 0 1 + M.corr 1 0 - M.corr 1 1

end LHVModel

/-- **CHSH inequality**: every local hidden-variable model satisfies `|CHSH| ≤ 2`. -/
theorem chsh_le_two {Ω : Type} [MeasurableSpace Ω] (M : LHVModel Ω) :
    |M.chsh| ≤ 2 := by
  haveI := M.isProb
  have h00 := M.intAB 0 0
  have h01 := M.intAB 0 1
  have h10 := M.intAB 1 0
  have h11 := M.intAB 1 1
  simp only [LHVModel.chsh, LHVModel.corr] at *
  norm_num at h00 h01 h10 h11 ⊢
  have hsum2 : Integrable (fun ω => M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω) M.μ := h00.add h01
  have hsum3 : Integrable
      (fun ω => M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω) M.μ := hsum2.add h10
  have hsum4 : Integrable
      (fun ω => M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω - M.A₂ ω * M.B₂ ω) M.μ :=
    hsum3.sub h11
  have hsplit : ∫ ω, (M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω
      - M.A₂ ω * M.B₂ ω) ∂M.μ
      = (∫ ω, M.A₁ ω * M.B₁ ω ∂M.μ) + (∫ ω, M.A₁ ω * M.B₂ ω ∂M.μ)
        + (∫ ω, M.A₂ ω * M.B₁ ω ∂M.μ) - (∫ ω, M.A₂ ω * M.B₂ ω ∂M.μ) := by
    rw [integral_sub hsum3 h11, integral_add hsum2 h10, integral_add h00 h01]
  rw [← hsplit]
  refine (abs_integral_le_integral_abs).trans ?_
  have hbound : ∀ ω, |M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω
      - M.A₂ ω * M.B₂ ω| ≤ 2 := fun ω =>
    chsh_pointwise _ _ _ _ (M.hA₁ ω) (M.hA₂ ω) (M.hB₁ ω) (M.hB₂ ω)
  calc ∫ ω, |M.A₁ ω * M.B₁ ω + M.A₁ ω * M.B₂ ω + M.A₂ ω * M.B₁ ω - M.A₂ ω * M.B₂ ω| ∂M.μ
      ≤ ∫ _ω, (2 : ℝ) ∂M.μ := by
        exact integral_mono hsum4.abs (integrable_const 2) hbound
    _ = 2 := by simp

/-- A local hidden-variable model on a one-point hidden-variable space, all outcomes `+1`.
It witnesses that the notion of a local hidden-variable model is not vacuous, and that the
classical CHSH bound `2` is attained. -/
noncomputable def trivialLHV : LHVModel Unit where
  μ := Measure.dirac ()
  isProb := inferInstance
  A₁ := fun _ => 1
  A₂ := fun _ => 1
  B₁ := fun _ => 1
  B₂ := fun _ => 1
  hA₁ := by norm_num
  hA₂ := by norm_num
  hB₁ := by norm_num
  hB₂ := by norm_num
  intAB := by
    intro i j
    simp

/-- The classical CHSH bound is attained, hence sharp. -/
theorem trivialLHV_chsh : trivialLHV.chsh = 2 := by
  simp [LHVModel.chsh, LHVModel.corr, trivialLHV]
  norm_num

/-- Quantum mechanics predicts, for the singlet state, the correlation `cos θ` where `θ` is the
angle between the two measurement directions. At the optimal CHSH angles the four correlations
are `√2/2, √2/2, √2/2, -√2/2`, with CHSH value `2√2`, which exceeds the classical bound `2`. -/
theorem quantum_chsh_value :
    Real.cos (Real.pi / 4) + Real.cos (Real.pi / 4) + Real.cos (Real.pi / 4)
      - Real.cos (3 * Real.pi / 4) = 2 * Real.sqrt 2 ∧ 2 < 2 * Real.sqrt 2 := by
  have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have hcos3 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, hcos]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨by rw [hcos, hcos3]; ring, ?_⟩
  nlinarith [hs, Real.sqrt_nonneg 2]

/-- **Bell's theorem**: no local hidden-variable model reproduces the quantum-mechanical
correlations of the singlet state at the optimal CHSH measurement angles, namely
`E(1,1) = E(1,2) = E(2,1) = √2/2` and `E(2,2) = -√2/2`, whose CHSH value is `2√2 > 2`. -/
theorem bell_theorem :
    ¬ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (M : LHVModel Ω),
        M.corr 0 0 = Real.sqrt 2 / 2 ∧ M.corr 0 1 = Real.sqrt 2 / 2 ∧
        M.corr 1 0 = Real.sqrt 2 / 2 ∧ M.corr 1 1 = -(Real.sqrt 2 / 2) := by
  rintro ⟨Ω, _, M, h00, h01, h10, h11⟩
  have hbound := chsh_le_two M
  have hval : M.chsh = 2 * Real.sqrt 2 := by
    simp only [LHVModel.chsh, h00, h01, h10, h11]; ring
  rw [hval, abs_of_nonneg (by positivity)] at hbound
  linarith [quantum_chsh_value.2]

end Frontier

#print axioms Frontier.bell_theorem
#print axioms Frontier.chsh_le_two

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

