/-
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## Local realism

A local hidden-variable (local realistic) model for a bipartite experiment with two
binary settings per side is a probability space `Ω` (the hidden variable) together with
four `Bool`-valued functions `A₁ A₂ B₁ B₂ : Ω → Bool`: the value `Aᵢ ω` is the outcome
Alice gets when she chooses setting `i`, and it depends only on the hidden variable and
on her own setting (locality), and it is defined for every `ω` regardless of which
setting is actually measured (realism).

Hardy's argument shows that the following four statements are inconsistent:

* `μ {A₁ = 1 ∧ B₂ = 1} = 0`,
* `μ {A₂ = 1 ∧ B₁ = 1} = 0`,
* `μ {A₁ = 0 ∧ B₁ = 0} = 0`,
* `μ {A₂ = 1 ∧ B₂ = 1} > 0`,

even though quantum mechanics predicts exactly this behaviour for a suitable entangled
state and suitable measurements (see `QI.hardy_quantum_witness` below).  No inequality
is involved: a nonzero *fraction of runs* (here `1/12` of them) already refutes local
realism.
-/

/-- **Hardy's zero lemma.** In any local realistic model, the three Hardy null
conditions force the Hardy event `A₂ = 1 ∧ B₂ = 1` to have probability zero. -/

theorem hardy_local_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Ω → Bool)
    (h₁ : μ {ω | A₁ ω = true ∧ B₂ ω = true} = 0)
    (h₂ : μ {ω | A₂ ω = true ∧ B₁ ω = true} = 0)
    (h₃ : μ {ω | A₁ ω = false ∧ B₁ ω = false} = 0) :
    μ {ω | A₂ ω = true ∧ B₂ ω = true} = 0 := by
  have hsub : {ω | A₂ ω = true ∧ B₂ ω = true} ⊆
      ({ω | A₁ ω = true ∧ B₂ ω = true} ∪ {ω | A₂ ω = true ∧ B₁ ω = true}) ∪
        {ω | A₁ ω = false ∧ B₁ ω = false} := by
    rintro ω ⟨ha₂, hb₂⟩
    rcases Bool.eq_false_or_eq_true (A₁ ω) with ha₁ | ha₁
    · exact Or.inl (Or.inl ⟨ha₁, hb₂⟩)
    · rcases Bool.eq_false_or_eq_true (B₁ ω) with hb₁ | hb₁
      · exact Or.inl (Or.inr ⟨ha₂, hb₁⟩)
      · exact Or.inr ⟨ha₁, hb₁⟩
  have hle := measure_mono (μ := μ) hsub
  have hunion : μ (({ω | A₁ ω = true ∧ B₂ ω = true} ∪ {ω | A₂ ω = true ∧ B₁ ω = true}) ∪
      {ω | A₁ ω = false ∧ B₁ ω = false}) = 0 := by
    refine measure_union_null (measure_union_null h₁ h₂) h₃
  exact le_antisymm (hunion ▸ hle) (zero_le _)

/-- **Hardy's paradox (local realism side).** No local hidden-variable model can satisfy
the three Hardy null conditions while assigning a strictly positive probability -- a
nonzero fraction of runs -- to the Hardy event `A₂ = 1 ∧ B₂ = 1`. -/
