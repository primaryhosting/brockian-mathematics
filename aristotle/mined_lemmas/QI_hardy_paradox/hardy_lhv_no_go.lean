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
