/-
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede every command, including module doc comments `/-! -/`,
-- so the required header appears above as an ordinary block comment and is repeated as the
-- module docstring immediately after the imports.)

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

open MeasureTheory

namespace QI

/-!
## Part 1: the local-realistic (hidden-variable) side

A local hidden-variable model for a two-party, two-settings-per-party experiment is a
probability space `Ω` (the space of hidden variables / runs) together with four outcome
functions

* `A₁ A₂ : Ω → Bool` — Alice's outcome for her setting `1` resp. `2`,
* `B₁ B₂ : Ω → Bool` — Bob's outcome for his setting `1` resp. `2`.

Locality and realism are encoded structurally: each outcome is a function of the run `ω`
alone, and in particular Alice's outcome does not depend on Bob's setting and vice versa.
Hardy's argument shows that the four Hardy conditions are then contradictory — a
*logical* (inequality-free) obstruction, unlike CHSH.
-/

/-- The pointwise (run-by-run) core of Hardy's argument: any run in which Alice's second
outcome and Bob's second outcome are both `true` must lie in one of the three Hardy
"forbidden" events. -/
theorem hardy_subset {Ω : Type*} (A₁ A₂ B₁ B₂ : Ω → Bool) :
    {ω | A₂ ω = true ∧ B₂ ω = true} ⊆
      ({ω | A₂ ω = true ∧ B₁ ω = false} ∪ {ω | A₁ ω = false ∧ B₂ ω = true})
        ∪ {ω | A₁ ω = true ∧ B₁ ω = true} := by
  rintro ω ⟨h2, h2'⟩
  cases hb : B₁ ω
  · exact Or.inl (Or.inl ⟨h2, hb⟩)
  · cases ha : A₁ ω
    · exact Or.inl (Or.inr ⟨ha, h2'⟩)
    · exact Or.inr ⟨ha, hb⟩

/-- Quantitative form of Hardy's argument in any hidden-variable model: the "Hardy event"
`A₂ = true ∧ B₂ = true` is contained in the union of the three events that Hardy's
conditions force to have probability zero, so its probability is bounded by their sum. -/
theorem hardy_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A₁ A₂ B₁ B₂ : Ω → Bool) :
    μ {ω | A₂ ω = true ∧ B₂ ω = true} ≤
      μ {ω | A₂ ω = true ∧ B₁ ω = false}
      + μ {ω | A₁ ω = false ∧ B₂ ω = true}
      + μ {ω | A₁ ω = true ∧ B₁ ω = true} := by
  calc μ {ω | A₂ ω = true ∧ B₂ ω = true}
      ≤ _ := measure_mono (hardy_subset A₁ A₂ B₁ B₂)
    _ ≤ _ := le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)

/-- **Hardy's paradox.**  No local hidden-variable model can reproduce Hardy's four
conditions:

* `A₂ = true` always forces `B₁ = true` (the event `A₂ = true ∧ B₁ = false` is null),
* `B₂ = true` always forces `A₁ = true` (the event `A₁ = false ∧ B₂ = true` is null),
* `A₁ = true ∧ B₁ = true` never happens (null event),
* yet a positive fraction of runs has `A₂ = true ∧ B₂ = true`.

Chaining the first three implications on any run of the (positive-probability) fourth
event yields `A₁ = true ∧ B₁ = true`, a contradiction — no inequality is needed. -/
theorem hardy_paradox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Ω → Bool)
    (h₁ : μ {ω | A₂ ω = true ∧ B₁ ω = false} = 0)
    (h₂ : μ {ω | A₁ ω = false ∧ B₂ ω = true} = 0)
    (h₃ : μ {ω | A₁ ω = true ∧ B₁ ω = true} = 0)
    (h₄ : 0 < μ {ω | A₂ ω = true ∧ B₂ ω = true}) : False := by
  have hle := hardy_bound μ A₁ A₂ B₁ B₂
  rw [h₁, h₂, h₃] at hle
  simp only [add_zero, nonpos_iff_eq_zero] at hle
  exact absurd hle h₄.ne'

/-- Equivalent formulation of `QI.hardy_paradox`: under the three Hardy null conditions,
*every* local hidden-variable model assigns probability exactly zero to the Hardy event. -/
theorem hardy_prob_eq_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Ω → Bool)
    (h₁ : μ {ω | A₂ ω = true ∧ B₁ ω = false} = 0)
    (h₂ : μ {ω | A₁ ω = false ∧ B₂ ω = true} = 0)
    (h₃ : μ {ω | A₁ ω = true ∧ B₁ ω = true} = 0) :
    μ {ω | A₂ ω = true ∧ B₂ ω = true} = 0 := by
  by_contra h
  exact hardy_paradox μ A₁ A₂ B₁ B₂ h₁ h₂ h₃ (pos_iff_ne_zero.mpr h)

/-!
## Part 2: the quantum side — a positive fraction of runs

Quantum mechanics satisfies the three Hardy null conditions while giving the Hardy event
probability `1/12 > 0`; by Part 1 that fraction of runs has no local-realistic
explanation.

We work with an explicit two-qubit system, `Fin 2 → Fin 2 → ℂ` (amplitudes `ψ i j` in the
product basis).  Probabilities are given by the Born rule, written here in a
normalisation-free way: for a (nonzero) state `ψ` and local vectors `a`, `b`,
`bornProb ψ a b = |⟨a ⊗ b, ψ⟩|² / (‖ψ‖² ‖a‖² ‖b‖²)`, which is the usual Born probability
`|⟨a ⊗ b, ψ⟩|²` once `ψ`, `a`, `b` are unit vectors.
-/

/-- The amplitude `⟨a ⊗ b, ψ⟩` of the product vector `a ⊗ b` in the two-qubit state `ψ`. -/
noncomputable def amp (psi : Fin 2 → Fin 2 → ℂ) (a b : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (a i) * (starRingEnd ℂ) (b j) * psi i j

/-- Squared norm of a one-qubit vector. -/
noncomputable def sqNorm (v : Fin 2 → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- Squared norm of a two-qubit state. -/
noncomputable def sqNorm2 (psi : Fin 2 → Fin 2 → ℂ) : ℝ := ∑ i, ∑ j, ‖psi i j‖ ^ 2

/-- Born-rule probability of the joint outcome described by the local vectors `a` (Alice)
and `b` (Bob) in the two-qubit state `psi`, written without assuming normalisation. -/
noncomputable def bornProb (psi : Fin 2 → Fin 2 → ℂ) (a b : Fin 2 → ℂ) : ℝ :=
  ‖amp psi a b‖ ^ 2 / (sqNorm2 psi * sqNorm a * sqNorm b)

/-- Hardy's two-qubit state `-|00⟩ + |01⟩ + |10⟩` (unnormalised; its squared norm is `3`). -/
noncomputable def hardyState : Fin 2 → Fin 2 → ℂ := ![![-1, 1], ![1, 0]]

/-- Outcome vector `|1⟩` for the first setting: outcome `true`. -/
def vT1 : Fin 2 → ℂ := ![0, 1]

/-- Outcome vector `|0⟩` for the first setting: outcome `false`. -/
def vF1 : Fin 2 → ℂ := ![1, 0]

/-- Outcome vector `|0⟩ + |1⟩` for the second setting: outcome `true`. -/
def vT2 : Fin 2 → ℂ := ![1, 1]

/-- Outcome vector `|0⟩ - |1⟩` for the second setting: outcome `false`. -/
def vF2 : Fin 2 → ℂ := ![1, -1]

/-- The first setting really is a measurement: its two outcome vectors are orthogonal. -/
theorem inner_vT1_vF1 : ∑ i, (starRingEnd ℂ) (vT1 i) * vF1 i = 0 := by
  simp [vT1, vF1, Fin.sum_univ_succ]

/-- The second setting really is a measurement: its two outcome vectors are orthogonal. -/
theorem inner_vT2_vF2 : ∑ i, (starRingEnd ℂ) (vT2 i) * vF2 i = 0 := by
  simp [vT2, vF2, Fin.sum_univ_succ]

/-- Hardy condition: `P(A₁ = true, B₁ = true) = 0`. -/
theorem hardy_quantum_T1T1 : bornProb hardyState vT1 vT1 = 0 := by
  simp [bornProb, amp, hardyState, vT1, Fin.sum_univ_succ]

/-- Hardy condition: `P(A₂ = true, B₁ = false) = 0`, i.e. `A₂ = true` forces `B₁ = true`. -/
theorem hardy_quantum_T2F1 : bornProb hardyState vT2 vF1 = 0 := by
  simp [bornProb, amp, hardyState, vT2, vF1, Fin.sum_univ_succ]

/-- Hardy condition: `P(A₁ = false, B₂ = true) = 0`, i.e. `B₂ = true` forces `A₁ = true`. -/
theorem hardy_quantum_F1T2 : bornProb hardyState vF1 vT2 = 0 := by
  simp [bornProb, amp, hardyState, vF1, vT2, Fin.sum_univ_succ]

/-- The Hardy event has quantum probability `1/12`: a positive fraction of runs which, by
`QI.hardy_paradox`, admits no local-realistic explanation. -/
theorem hardy_quantum_T2T2 : bornProb hardyState vT2 vT2 = 1 / 12 := by
  simp [bornProb, amp, sqNorm, sqNorm2, hardyState, vT2, Fin.sum_univ_succ]
  norm_num

/-- Summary of the quantum side: the three Hardy null conditions hold exactly, while the
Hardy event occurs in a fraction `1/12 > 0` of the runs. -/
theorem hardy_quantum_violation :
    bornProb hardyState vT1 vT1 = 0 ∧
    bornProb hardyState vT2 vF1 = 0 ∧
    bornProb hardyState vF1 vT2 = 0 ∧
    0 < bornProb hardyState vT2 vT2 :=
  ⟨hardy_quantum_T1T1, hardy_quantum_T2F1, hardy_quantum_F1T2, by
    rw [hardy_quantum_T2T2]; norm_num⟩

end QI

#print axioms QI.hardy_paradox
#print axioms QI.hardy_prob_eq_zero
#print axioms QI.hardy_quantum_violation
#print axioms QI.hardy_quantum_T2T2
#print axioms QI.hardy_bound

