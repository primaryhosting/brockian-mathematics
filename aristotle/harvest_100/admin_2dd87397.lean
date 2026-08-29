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

/-!
## Part 1: local realism

A *local deterministic hidden-variable model* for a two-party, two-setting,
two-outcome experiment is a probability space `(Ω, μ)` (the hidden variable)
together with response functions `a₁ a₂ b₁ b₂ : Ω → Bool`: `aᵢ ω` is Alice's
outcome when she chooses setting `i` and the hidden variable is `ω` (and it does
not depend on Bob's setting), similarly for Bob.

Hardy's argument shows that the three "impossibility" constraints

* `a₁ = 1` and `b₂ = 1` never happens,
* `a₂ = 1` and `b₁ = 1` never happens,
* `a₁ = 0` and `b₁ = 0` never happens,

force the *Hardy event* `a₂ = 1 ∧ b₂ = 1` to have probability `0`.
No inequality is involved: a single run of the Hardy event already refutes the model.
-/

/-- The key combinatorial step of Hardy's argument: in any local deterministic
model, the Hardy event is contained in the union of the three forbidden events. -/
theorem hardy_event_subset {Ω : Type*} (a₁ a₂ b₁ b₂ : Ω → Bool) :
    {ω | a₂ ω = true ∧ b₂ ω = true} ⊆
      {ω | a₁ ω = true ∧ b₂ ω = true} ∪ {ω | a₂ ω = true ∧ b₁ ω = true} ∪
        {ω | a₁ ω = false ∧ b₁ ω = false} := by
  rintro ω ⟨ha₂, hb₂⟩
  by_cases hb₁ : b₁ ω = true
  · exact Or.inl (Or.inr ⟨ha₂, hb₁⟩)
  · by_cases ha₁ : a₁ ω = true
    · exact Or.inl (Or.inl ⟨ha₁, hb₂⟩)
    · exact Or.inr ⟨Bool.eq_false_iff.mpr ha₁, Bool.eq_false_iff.mpr hb₁⟩

/-- **Hardy's argument, local-realistic side.**  In any local deterministic
hidden-variable model satisfying the three Hardy constraints, the Hardy event
`a₂ = 1 ∧ b₂ = 1` occurs with probability zero. -/
theorem hardy_local_realism {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a₁ a₂ b₁ b₂ : Ω → Bool)
    (h₁ : μ {ω | a₁ ω = true ∧ b₂ ω = true} = 0)
    (h₂ : μ {ω | a₂ ω = true ∧ b₁ ω = true} = 0)
    (h₃ : μ {ω | a₁ ω = false ∧ b₁ ω = false} = 0) :
    μ {ω | a₂ ω = true ∧ b₂ ω = true} = 0 := by
  refine measure_mono_null (hardy_event_subset a₁ a₂ b₁ b₂) ?_
  exact measure_union_null (measure_union_null h₁ h₂) h₃

/-- Real-valued version of `QI.hardy_local_realism`, for a probability measure. -/
theorem hardy_local_realism_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a₁ a₂ b₁ b₂ : Ω → Bool)
    (h₁ : μ.real {ω | a₁ ω = true ∧ b₂ ω = true} = 0)
    (h₂ : μ.real {ω | a₂ ω = true ∧ b₁ ω = true} = 0)
    (h₃ : μ.real {ω | a₁ ω = false ∧ b₁ ω = false} = 0) :
    μ.real {ω | a₂ ω = true ∧ b₂ ω = true} = 0 := by
  have key : ∀ s : Set Ω, μ.real s = 0 → μ s = 0 := by
    intro s hs
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hs
    exact hs.resolve_right (measure_ne_top μ s)
  rw [measureReal_def, hardy_local_realism μ a₁ a₂ b₁ b₂ (key _ h₁) (key _ h₂) (key _ h₃),
    ENNReal.toReal_zero]

/-!
## Part 2: the quantum predictions

We work with an (unnormalised) two-qubit state `ψ : Fin 2 → Fin 2 → ℂ` and
(unnormalised) local measurement vectors `u v : Fin 2 → ℂ`.  The Born
probability of Alice and Bob jointly projecting onto `u` and `v` is

`bornProb ψ u v = |⟨u ⊗ v, ψ⟩|² / (‖ψ‖² ‖u‖² ‖v‖²)`.
-/

/-- Squared norm of a (unnormalised) qubit vector. -/
def qnorm (u : Fin 2 → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

/-- Squared norm of a (unnormalised) two-qubit state. -/
def snorm (ψ : Fin 2 → Fin 2 → ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (ψ i j)

/-- Amplitude `⟨u ⊗ v, ψ⟩` of the product vector `u ⊗ v` in the state `ψ`. -/
def amp (ψ : Fin 2 → Fin 2 → ℂ) (u v : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (u i) * (starRingEnd ℂ) (v j) * ψ i j

/-- Born probability that Alice's outcome is "along `u`" and Bob's is "along `v`". -/
def bornProb (ψ : Fin 2 → Fin 2 → ℂ) (u v : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (amp ψ u v) / (snorm ψ * qnorm u * qnorm v)

/-- Hardy's state: `|00⟩ + |01⟩ + |10⟩` (unnormalised). -/
def hardyState : Fin 2 → Fin 2 → ℂ := ![![1, 1], ![1, 0]]

/-- Alice's first measurement direction (outcome `1` for setting `1`). -/
def uOne : Fin 2 → ℂ := ![1, 0]

/-- The direction orthogonal to `uOne` (outcome `0` for setting `1`). -/
def uOnePerp : Fin 2 → ℂ := ![0, 1]

/-- Alice's second measurement direction (outcome `1` for setting `2`). -/
def uTwo : Fin 2 → ℂ := ![1, -1]

/-- Bob's first measurement direction (outcome `1` for setting `1`). -/
def vOne : Fin 2 → ℂ := ![1, 0]

/-- The direction orthogonal to `vOne` (outcome `0` for setting `1`). -/
def vOnePerp : Fin 2 → ℂ := ![0, 1]

/-- Bob's second measurement direction (outcome `1` for setting `2`). -/
def vTwo : Fin 2 → ℂ := ![1, -1]

private lemma expand (ψ : Fin 2 → Fin 2 → ℂ) (u v : Fin 2 → ℂ) :
    amp ψ u v =
      (starRingEnd ℂ) (u 0) * (starRingEnd ℂ) (v 0) * ψ 0 0 +
      (starRingEnd ℂ) (u 0) * (starRingEnd ℂ) (v 1) * ψ 0 1 +
      ((starRingEnd ℂ) (u 1) * (starRingEnd ℂ) (v 0) * ψ 1 0 +
        (starRingEnd ℂ) (u 1) * (starRingEnd ℂ) (v 1) * ψ 1 1) := by
  simp [amp, Fin.sum_univ_two, add_assoc]

/-- The first Hardy constraint holds exactly in the quantum model. -/
theorem hardy_quantum_one : bornProb hardyState uOne vTwo = 0 := by
  have h : amp hardyState uOne vTwo = 0 := by
    rw [expand]
    simp [hardyState, uOne, vTwo]
    norm_num
  simp [bornProb, h]

/-- The second Hardy constraint holds exactly in the quantum model. -/
theorem hardy_quantum_two : bornProb hardyState uTwo vOne = 0 := by
  have h : amp hardyState uTwo vOne = 0 := by
    rw [expand]
    simp [hardyState, uTwo, vOne]
    norm_num
  simp [bornProb, h]

/-- The third Hardy constraint holds exactly in the quantum model. -/
theorem hardy_quantum_three : bornProb hardyState uOnePerp vOnePerp = 0 := by
  have h : amp hardyState uOnePerp vOnePerp = 0 := by
    rw [expand]
    simp [hardyState, uOnePerp, vOnePerp]
  simp [bornProb, h]

/-- Quantum mechanics nevertheless predicts that the Hardy event occurs in a
positive fraction (exactly `1/12`) of the runs. -/
theorem hardy_quantum_fraction : bornProb hardyState uTwo vTwo = 1 / 12 := by
  have h : amp hardyState uTwo vTwo = -1 := by
    rw [expand]
    simp [hardyState, uTwo, vTwo]
    norm_num
  have hs : snorm hardyState = 3 := by
    simp [snorm, hardyState, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  have hu : qnorm uTwo = 2 := by
    simp [qnorm, uTwo, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  have hv : qnorm vTwo = 2 := by
    simp [qnorm, vTwo, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  rw [bornProb, h, hs, hu, hv]
  norm_num

/-!
## Part 3: the paradox
-/

/-- **Hardy's paradox.**

Quantum mechanics predicts, for the Hardy state `|00⟩ + |01⟩ + |10⟩` and the
indicated local measurement directions, that

* the three Hardy events `(a₁ = 1, b₂ = 1)`, `(a₂ = 1, b₁ = 1)`, `(a₁ = 0, b₁ = 0)`
  never occur, while
* the Hardy event `(a₂ = 1, b₂ = 1)` occurs in a fraction `1/12 > 0` of the runs.

No local deterministic hidden-variable model can reproduce these four numbers:
the three vanishing probabilities force the fourth to vanish as well.  Thus a
positive fraction of the runs — those in the Hardy event — witnesses the
failure of local realism directly, with no inequality involved. -/
theorem hardy_paradox :
    -- the quantum predictions
    bornProb hardyState uOne vTwo = 0 ∧
    bornProb hardyState uTwo vOne = 0 ∧
    bornProb hardyState uOnePerp vOnePerp = 0 ∧
    0 < bornProb hardyState uTwo vTwo ∧
    -- no local deterministic hidden-variable model reproduces them
    ¬ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (a₁ a₂ b₁ b₂ : Ω → Bool),
        μ.real {ω | a₁ ω = true ∧ b₂ ω = true} = bornProb hardyState uOne vTwo ∧
        μ.real {ω | a₂ ω = true ∧ b₁ ω = true} = bornProb hardyState uTwo vOne ∧
        μ.real {ω | a₁ ω = false ∧ b₁ ω = false} = bornProb hardyState uOnePerp vOnePerp ∧
        μ.real {ω | a₂ ω = true ∧ b₂ ω = true} = bornProb hardyState uTwo vTwo := by
  refine ⟨hardy_quantum_one, hardy_quantum_two, hardy_quantum_three, ?_, ?_⟩
  · rw [hardy_quantum_fraction]; norm_num
  · rintro ⟨Ω, _, μ, hμ, a₁, a₂, b₁, b₂, h₁, h₂, h₃, h₄⟩
    rw [hardy_quantum_one] at h₁
    rw [hardy_quantum_two] at h₂
    rw [hardy_quantum_three] at h₃
    rw [hardy_quantum_fraction] at h₄
    rw [hardy_local_realism_real μ a₁ a₂ b₁ b₂ h₁ h₂ h₃] at h₄
    norm_num at h₄

end QI

