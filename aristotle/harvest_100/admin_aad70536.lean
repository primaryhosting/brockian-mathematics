import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
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

namespace QI

open MeasureTheory

/-! ## The local hidden variable (local realism) side

In a local hidden variable model every run of the experiment is described by a hidden
variable `ω`, and the outcome of each of the two possible measurements on each side is a
definite function of `ω`: `A₁, A₂ : Ω → Bool` for Alice and `B₁, B₂ : Ω → Bool` for Bob
(locality: Alice's outcomes do not depend on Bob's setting and vice versa). -/

/-- **Hardy's no-go for local realism.**  If the three "Hardy constraints" hold with
probability one, namely `P(A₁ = 1, B₂ = 1) = 0`, `P(A₂ = 1, B₁ = 1) = 0` and
`P(A₂ = 0, B₂ = 0) = 0`, then the Hardy event `A₁ = 1, B₁ = 1` must have probability
zero.  (The pointwise argument: if `A₁ ω = 1` and `B₁ ω = 1`, then `B₂ ω = 0` by the
first constraint and `A₂ ω = 0` by the second, contradicting the third.) -/
theorem hardy_lhv_no_go {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Ω → Bool)
    (h₁ : μ {ω : Ω | A₁ ω = true ∧ B₂ ω = true} = 0)
    (h₂ : μ {ω : Ω | A₂ ω = true ∧ B₁ ω = true} = 0)
    (h₃ : μ {ω : Ω | A₂ ω = false ∧ B₂ ω = false} = 0) :
    μ {ω : Ω | A₁ ω = true ∧ B₁ ω = true} = 0 := by
  have hsub : {ω : Ω | A₁ ω = true ∧ B₁ ω = true} ⊆
      {ω : Ω | A₁ ω = true ∧ B₂ ω = true} ∪
        ({ω : Ω | A₂ ω = true ∧ B₁ ω = true} ∪ {ω : Ω | A₂ ω = false ∧ B₂ ω = false}) := by
    rintro ω ⟨ha, hb⟩
    rcases Bool.eq_false_or_eq_true (B₂ ω) with hb2 | hb2
    · exact Or.inl ⟨ha, hb2⟩
    · rcases Bool.eq_false_or_eq_true (A₂ ω) with ha2 | ha2
      · exact Or.inr (Or.inl ⟨ha2, hb⟩)
      · exact Or.inr (Or.inr ⟨ha2, hb2⟩)
  refine le_antisymm ?_ (zero_le _)
  calc μ {ω : Ω | A₁ ω = true ∧ B₁ ω = true} ≤ _ := measure_mono hsub
    _ ≤ 0 := by
        refine le_trans (measure_union_le _ _) ?_
        simp [h₁, h₂, h₃]

/-! ## The quantum side: an explicit Hardy state and measurements -/

/-- Amplitude `⟨u ⊗ v, ψ⟩` for a two-qubit state `ψ` and local vectors `u`, `v`. -/
noncomputable def amp (u v : Fin 2 → ℂ) (psi : Fin 2 → Fin 2 → ℂ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (u i) * (starRingEnd ℂ) (v j) * psi i j

/-- Born-rule probability of the joint outcome described by the local unit vectors
`u` (Alice) and `v` (Bob) on the state `psi`. -/
noncomputable def prob (u v : Fin 2 → ℂ) (psi : Fin 2 → Fin 2 → ℂ) : ℝ :=
  Complex.normSq (amp u v psi)

/-- The Hardy state `(|00⟩ + |01⟩ + |10⟩)/√3`. -/
noncomputable def hardyState : Fin 2 → Fin 2 → ℂ :=
  ![![((Real.sqrt 3)⁻¹ : ℝ), ((Real.sqrt 3)⁻¹ : ℝ)], ![((Real.sqrt 3)⁻¹ : ℝ), 0]]

/-- Outcome `1` vector of the first measurement setting, `(|1⟩ - |0⟩)/√2`
(the same setting is used by Alice and by Bob). -/
noncomputable def m1one : Fin 2 → ℂ :=
  ![((-((Real.sqrt 2)⁻¹) : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]

/-- Outcome `0` vector of the first measurement setting, `(|0⟩ + |1⟩)/√2`. -/
noncomputable def m1zero : Fin 2 → ℂ :=
  ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]

/-- Outcome `1` vector of the second measurement setting, `|0⟩`. -/
def m2one : Fin 2 → ℂ := ![1, 0]

/-- Outcome `0` vector of the second measurement setting, `|1⟩`. -/
def m2zero : Fin 2 → ℂ := ![0, 1]

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 := by positivity

private theorem sqrt_three_ne : Real.sqrt 3 ≠ 0 := by positivity

/-- The Hardy state is a unit vector. -/
theorem hardyState_normalized :
    ∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq (hardyState i j) = 1 := by
  have h3 := sqrt_three_sq
  have h3' := sqrt_three_ne
  simp [Fin.sum_univ_two, hardyState, Complex.normSq_ofReal]
  field_simp
  linarith [h3]

/-- The two outcome vectors of the first setting form an orthonormal basis of `ℂ²`. -/
theorem m1_orthonormal :
    (∑ i : Fin 2, Complex.normSq (m1one i)) = 1 ∧
      (∑ i : Fin 2, Complex.normSq (m1zero i)) = 1 ∧
      (∑ i : Fin 2, (starRingEnd ℂ) (m1one i) * m1zero i) = 0 := by
  have h2 := sqrt_two_sq
  have h2' := sqrt_two_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_two, m1one, m1zero, Complex.normSq_ofReal] <;>
    field_simp <;> linarith [h2]

/-- The two outcome vectors of the second setting form an orthonormal basis of `ℂ²`. -/
theorem m2_orthonormal :
    (∑ i : Fin 2, Complex.normSq (m2one i)) = 1 ∧
      (∑ i : Fin 2, Complex.normSq (m2zero i)) = 1 ∧
      (∑ i : Fin 2, (starRingEnd ℂ) (m2one i) * m2zero i) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_two, m2one, m2zero]

/-- `P(A₁ = 1, B₂ = 1) = 0` for the Hardy state. -/
theorem prob_one_two : prob m1one m2one hardyState = 0 := by
  simp [prob, amp, Fin.sum_univ_two, hardyState, m1one, m2one]

/-- `P(A₂ = 1, B₁ = 1) = 0` for the Hardy state. -/
theorem prob_two_one : prob m2one m1one hardyState = 0 := by
  simp [prob, amp, Fin.sum_univ_two, hardyState, m1one, m2one]

/-- `P(A₂ = 0, B₂ = 0) = 0` for the Hardy state. -/
theorem prob_two_two_zero : prob m2zero m2zero hardyState = 0 := by
  simp [prob, amp, Fin.sum_univ_two, hardyState, m2zero]

/-- The Hardy event occurs in a positive fraction `1/12` of the runs. -/
theorem prob_one_one : prob m1one m1one hardyState = 1 / 12 := by
  have h2 := sqrt_two_sq
  have h3 := sqrt_three_sq
  have h2' := sqrt_two_ne
  have h3' := sqrt_three_ne
  have h24 : Real.sqrt 2 ^ 4 = 4 := by nlinarith [h2]
  have hamp : amp m1one m1one hardyState
      = ((-((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt 3)⁻¹) : ℝ) : ℂ) := by
    simp [amp, Fin.sum_univ_two, hardyState, m1one]
  rw [prob, hamp, Complex.normSq_ofReal]
  field_simp
  rw [h24, h3]
  norm_num

/-- The Hardy event has strictly positive quantum probability. -/
theorem prob_one_one_pos : 0 < prob m1one m1one hardyState := by
  rw [prob_one_one]; norm_num

/-- Sanity check (Parseval / normalization of the Born rule): the four joint outcome
probabilities for the setting pair `(1, 1)` sum to `1`, so `1/12` really is the fraction
of runs in which the Hardy event occurs. -/
theorem probs_setting_one_one_sum :
    prob m1one m1one hardyState + prob m1one m1zero hardyState +
      prob m1zero m1one hardyState + prob m1zero m1zero hardyState = 1 := by
  have h2 := sqrt_two_sq
  have h3 := sqrt_three_sq
  have h2' := sqrt_two_ne
  have h3' := sqrt_three_ne
  have h24 : Real.sqrt 2 ^ 4 = 4 := by nlinarith [h2]
  simp [prob, amp, Fin.sum_univ_two, hardyState, m1one, m1zero, Complex.normSq_apply]
  field_simp
  ring_nf
  nlinarith [h2, h3, h24]

/-! ## The paradox -/

/-- **Hardy's paradox.**  No local hidden variable model can reproduce the four
quantum-mechanical probabilities of the Hardy state: the three vanishing probabilities
force the Hardy event to have probability `0` in any local model, whereas quantum
mechanics predicts that it occurs in a fraction `1/12 > 0` of the runs. -/
theorem hardy_paradox :
    ¬ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (A₁ A₂ B₁ B₂ : Ω → Bool),
        μ {ω : Ω | A₁ ω = true ∧ B₂ ω = true} =
            ENNReal.ofReal (prob m1one m2one hardyState) ∧
          μ {ω : Ω | A₂ ω = true ∧ B₁ ω = true} =
            ENNReal.ofReal (prob m2one m1one hardyState) ∧
          μ {ω : Ω | A₂ ω = false ∧ B₂ ω = false} =
            ENNReal.ofReal (prob m2zero m2zero hardyState) ∧
          μ {ω : Ω | A₁ ω = true ∧ B₁ ω = true} =
            ENNReal.ofReal (prob m1one m1one hardyState) := by
  rintro ⟨Ω, _, μ, A₁, A₂, B₁, B₂, hq₁, hq₂, hq₃, hq₄⟩
  have e₁ : μ {ω : Ω | A₁ ω = true ∧ B₂ ω = true} = 0 := by
    rw [hq₁, prob_one_two, ENNReal.ofReal_zero]
  have e₂ : μ {ω : Ω | A₂ ω = true ∧ B₁ ω = true} = 0 := by
    rw [hq₂, prob_two_one, ENNReal.ofReal_zero]
  have e₃ : μ {ω : Ω | A₂ ω = false ∧ B₂ ω = false} = 0 := by
    rw [hq₃, prob_two_two_zero, ENNReal.ofReal_zero]
  have e₄ : μ {ω : Ω | A₁ ω = true ∧ B₁ ω = true} = 0 :=
    hardy_lhv_no_go μ A₁ A₂ B₁ B₂ e₁ e₂ e₃
  rw [hq₄, prob_one_one] at e₄
  rw [ENNReal.ofReal_eq_zero] at e₄
  norm_num at e₄

end QI

