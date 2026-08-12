/-
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Statement: Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Statement: Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Finset

namespace QI

universe u

/-! ## Two-qubit kinematics

A two-qubit pure state is an array of amplitudes `psi : Fin 2 → Fin 2 → ℂ`, and a local
measurement outcome on each side is described by a unit vector in `ℂ²`.  The Born rule gives
the joint probability of the pair of outcomes `(u, v)` as `|⟪u ⊗ v, psi⟫|²`.
-/

/-- The amplitude `⟪u ⊗ v, psi⟫` of the product vector `u ⊗ v` in the two-qubit state `psi`. -/
noncomputable def amp (u v : Fin 2 → ℂ) (psi : Fin 2 → Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (u i) * (starRingEnd ℂ) (v j) * psi i j

/-- Born-rule probability of jointly obtaining the outcomes described by the unit vectors
`u` (Alice) and `v` (Bob) in the two-qubit state `psi`. -/
noncomputable def prob (u v : Fin 2 → ℂ) (psi : Fin 2 → Fin 2 → ℂ) : ℝ :=
  Complex.normSq (amp u v psi)

/-- The hermitian inner product of two vectors of `ℂ²`. -/
noncomputable def inner2 (u v : Fin 2 → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (u i) * v i

/-- `u` is a unit vector of `ℂ²`. -/
def IsUnitVec (u : Fin 2 → ℂ) : Prop := ∑ i, Complex.normSq (u i) = 1

/-- `psi` is a normalized two-qubit state. -/
def IsUnitState (psi : Fin 2 → Fin 2 → ℂ) : Prop :=
  ∑ i, ∑ j, Complex.normSq (psi i j) = 1

/-! ## The Hardy state and the Hardy measurements -/

/-- `1/√2`, as a complex number. -/
noncomputable def c2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- `1/√12`, as a complex number. -/
noncomputable def c12 : ℂ := ((Real.sqrt 12)⁻¹ : ℝ)

/-- The "+" outcome vector of Alice's first measurement setting (and of Bob's). -/
def v0 : Fin 2 → ℂ := ![1, 0]

/-- The "+" outcome vector of the second measurement setting. -/
noncomputable def v1 : Fin 2 → ℂ := ![c2, c2]

/-- The "−" outcome vector of the second measurement setting. -/
noncomputable def v1' : Fin 2 → ℂ := ![-c2, c2]

/-- Hardy's two-qubit state `(|00⟩ + |01⟩ + |10⟩ - 3|11⟩)/√12`. -/
noncomputable def hardyState : Fin 2 → Fin 2 → ℂ := ![![c12, c12], ![c12, -3 * c12]]

lemma normSq_c2 : Complex.normSq c2 = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [c2, Complex.normSq_ofReal]
  rw [← mul_inv, h]
  norm_num

lemma normSq_c12 : Complex.normSq c12 = 1 / 12 := by
  have h : Real.sqrt 12 * Real.sqrt 12 = 12 := Real.mul_self_sqrt (by norm_num)
  simp only [c12, Complex.normSq_ofReal]
  rw [← mul_inv, h]
  norm_num

lemma star_c2 : (starRingEnd ℂ) c2 = c2 := by
  simp [c2]

/-! ## The quantum predictions -/

lemma v0_unit : IsUnitVec v0 := by
  simp [IsUnitVec, v0, Fin.sum_univ_two]

lemma v1_unit : IsUnitVec v1 := by
  simp [IsUnitVec, v1, Fin.sum_univ_two, normSq_c2]
  norm_num

lemma v1'_unit : IsUnitVec v1' := by
  simp [IsUnitVec, v1', Fin.sum_univ_two, normSq_c2]
  norm_num

lemma v1_orthogonal : inner2 v1 v1' = 0 := by
  simp [inner2, v1, v1', Fin.sum_univ_two, star_c2]

lemma hardyState_unit : IsUnitState hardyState := by
  simp only [IsUnitState, hardyState, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show ((-3 : ℂ) * c12) = ((-3 : ℝ) : ℂ) * c12 by norm_num]
  rw [Complex.normSq_mul]
  simp [normSq_c12]
  norm_num

/-- Hardy's first zero: outcome `+` for Alice's setting 0 never occurs together with
outcome `−` for Bob's setting 1. -/
lemma hardy_zero_A0_B1' : prob v0 v1' hardyState = 0 := by
  have : amp v0 v1' hardyState = 0 := by
    simp only [amp, v0, v1', hardyState, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_neg, star_c2]
    simp
  simp [prob, this]

/-- Hardy's second zero: outcome `−` for Alice's setting 1 never occurs together with
outcome `+` for Bob's setting 0. -/
lemma hardy_zero_A1'_B0 : prob v1' v0 hardyState = 0 := by
  have : amp v1' v0 hardyState = 0 := by
    simp only [amp, v0, v1', hardyState, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_neg, star_c2]
    simp
  simp [prob, this]

/-- Hardy's third zero: the outcomes `+`/`+` for the two second settings never occur together. -/
lemma hardy_zero_A1_B1 : prob v1 v1 hardyState = 0 := by
  have : amp v1 v1 hardyState = 0 := by
    simp only [amp, v1, hardyState, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, star_c2]
    ring
  simp [prob, this]

/-- Hardy's positive event: in a fraction `1/12` of the runs both first settings give `+`. -/
lemma hardy_pos_A0_B0 : prob v0 v0 hardyState = 1 / 12 := by
  have : amp v0 v0 hardyState = c12 := by
    simp [amp, v0, hardyState, Fin.sum_univ_two]
  rw [prob, this, normSq_c12]

/-! ## The local hidden-variable no-go

In a local hidden-variable model, each run is described by a hidden state `x : Λ` which already
determines the outcome of every measurement.  `A0` (resp. `A1`) is the set of hidden states for
which Alice's setting 0 (resp. 1) yields the outcome `+`, and similarly for Bob; the complement
of such a set is the event that the outcome is `−`.  Probabilities of joint events are then
computed from a single measure `μ` on `Λ`.
-/

/-- **Hardy's argument, run by run.**  In a deterministic local hidden-variable model, where
`A i x = true` means that Alice's setting `i` yields the outcome `+` on the run with hidden state
`x` (and similarly for Bob), the three Hardy constraints are incompatible, on *every* run, with
both first settings yielding `+`.  No inequality is involved. -/
theorem lhv_hardy_pointwise {Λ : Type u} (A B : Fin 2 → Λ → Bool)
    (h1 : ∀ x, A 0 x = true → B 1 x = true)
    (h2 : ∀ x, B 0 x = true → A 1 x = true)
    (h3 : ∀ x, ¬(A 1 x = true ∧ B 1 x = true)) :
    ∀ x, ¬(A 0 x = true ∧ B 0 x = true) := by
  rintro x ⟨hA0, hB0⟩
  exact h3 x ⟨h2 x hB0, h1 x hA0⟩

/-- **The local realist prediction.**  If a local hidden-variable model reproduces Hardy's three
vanishing probabilities, then in that model the event "both first settings give `+`" has
probability zero. -/
theorem lhv_hardy_zero {Λ : Type u} [MeasurableSpace Λ] (μ : Measure Λ)
    (A0 A1 B0 B1 : Set Λ)
    (h1 : μ (A0 ∩ B1ᶜ) = 0) (h2 : μ (A1ᶜ ∩ B0) = 0) (h3 : μ (A1 ∩ B1) = 0) :
    μ (A0 ∩ B0) = 0 := by
  have hsub : A0 ∩ B0 ⊆ (A0 ∩ B1ᶜ) ∪ ((A1ᶜ ∩ B0) ∪ (A1 ∩ B1)) := by
    rintro x ⟨hA0, hB0⟩
    by_cases hB1 : x ∈ B1
    · by_cases hA1 : x ∈ A1
      · exact Or.inr (Or.inr ⟨hA1, hB1⟩)
      · exact Or.inr (Or.inl ⟨hA1, hB0⟩)
    · exact Or.inl ⟨hA0, hB1⟩
  refine measure_mono_null hsub ?_
  simp [h1, h2, h3, measure_union_null]

/-! ## Hardy's paradox -/

/-- **Hardy's paradox.**

* The first conjunct is the quantum-mechanical side: there is a genuine two-qubit state
  (Hardy's state) and genuine measurements — a unit vector `a0` for Alice's setting `0`, an
  orthonormal pair `a1, a1'` for her setting `1`, and likewise `b0`, `b1`, `b1'` for Bob —
  such that three joint outcome probabilities vanish (`+−` for `(0,1)`, `−+` for `(1,0)` and
  `++` for `(1,1)`) while the joint outcome `++` for the settings `(0,0)` occurs in a fraction
  `1/12 > 0` of the runs.

* The second conjunct is the local-realist side: no local hidden-variable model can reproduce
  these numbers.  Indeed the three vanishing probabilities force, run by run and without any
  inequality, the probability of the `++` event for the settings `(0,0)` to be exactly `0`,
  contradicting the quantum value `1/12`.

Hence a nonzero fraction of the runs witnesses the failure of local realism. -/
theorem hardy_paradox :
    (∃ (psi : Fin 2 → Fin 2 → ℂ) (a0 a1 a1' b0 b1 b1' : Fin 2 → ℂ),
        IsUnitState psi ∧
        IsUnitVec a0 ∧ IsUnitVec a1 ∧ IsUnitVec a1' ∧
        IsUnitVec b0 ∧ IsUnitVec b1 ∧ IsUnitVec b1' ∧
        inner2 a1 a1' = 0 ∧ inner2 b1 b1' = 0 ∧
        prob a0 b1' psi = 0 ∧ prob a1' b0 psi = 0 ∧ prob a1 b1 psi = 0 ∧
        prob a0 b0 psi = 1 / 12) ∧
    (∀ {Λ : Type u} [MeasurableSpace Λ] (μ : Measure Λ) (A0 A1 B0 B1 : Set Λ),
        μ (A0 ∩ B1ᶜ) = 0 → μ (A1ᶜ ∩ B0) = 0 → μ (A1 ∩ B1) = 0 →
        μ (A0 ∩ B0) = ENNReal.ofReal (1 / 12) → False) := by
  constructor
  · exact ⟨hardyState, v0, v1, v1', v0, v1, v1', hardyState_unit, v0_unit, v1_unit, v1'_unit,
      v0_unit, v1_unit, v1'_unit, v1_orthogonal, v1_orthogonal, hardy_zero_A0_B1',
      hardy_zero_A1'_B0, hardy_zero_A1_B1, hardy_pos_A0_B0⟩
  · intro Λ _ μ A0 A1 B0 B1 h1 h2 h3 h4
    have hzero := lhv_hardy_zero μ A0 A1 B0 B1 h1 h2 h3
    rw [hzero] at h4
    have : ENNReal.ofReal (1 / 12 : ℝ) ≠ 0 := by
      simp
    exact this h4.symm

end QI

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

