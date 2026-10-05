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

/-! ## Hardy's paradox for local hidden-variable models

A local hidden-variable model for a bipartite experiment with two binary settings and two
binary outcomes per party consists of a probability space `Ω` (the hidden variables) together
with outcome functions `A x ω` for Alice and `B y ω` for Bob.  *Locality* is encoded in the
types: Alice's outcome depends only on her own setting `x` and the hidden variable `ω`, never
on Bob's setting `y`, and symmetrically for Bob.

Hardy's argument shows that no such model can satisfy the four *Hardy conditions*:

* `A₁ = 1` implies `B₂ = 1` (almost surely),
* `B₁ = 1` implies `A₂ = 1` (almost surely),
* `A₂ = 1` and `B₂ = 1` never happen together (almost surely),
* yet `A₁ = 1` and `B₁ = 1` happen with nonzero probability.

Here the setting `false` stands for the first measurement and `true` for the second one, and
the outcome `true` stands for the outcome "1".
-/

/-- **Hardy's paradox.**  There is no local hidden-variable model satisfying the four Hardy
conditions.  Locality is built into the statement: Alice's outcome `A x ω` does not depend on
Bob's setting and Bob's outcome `B y ω` does not depend on Alice's setting.

The three "impossible" events have probability zero, while the event `A₁ = 1 ∧ B₁ = 1` has
nonzero probability; but that event is contained in the union of the three null events, a
contradiction.  No measurability assumptions are needed. -/

theorem hardy_paradox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Bool → Ω → Bool)
    (hA₁B₂ : μ {ω | A false ω = true ∧ B true ω = false} = 0)
    (hA₂B₁ : μ {ω | A true ω = false ∧ B false ω = true} = 0)
    (hA₂B₂ : μ {ω | A true ω = true ∧ B true ω = true} = 0)
    (hpos : μ {ω | A false ω = true ∧ B false ω = true} ≠ 0) :
    False := by
  apply hpos
  have hsub :
      {ω | A false ω = true ∧ B false ω = true} ⊆
        {ω | A false ω = true ∧ B true ω = false} ∪
          ({ω | A true ω = false ∧ B false ω = true} ∪
            {ω | A true ω = true ∧ B true ω = true}) := by
    intro ω hω
    obtain ⟨ha, hb⟩ := hω
    by_cases hb₂ : B true ω = true
    · by_cases ha₂ : A true ω = true
      · exact Or.inr (Or.inr ⟨ha₂, hb₂⟩)
      · exact Or.inr (Or.inl ⟨by simpa using ha₂, hb⟩)
    · exact Or.inl ⟨ha, by simpa using hb₂⟩
  refine le_antisymm ?_ (zero_le _)
  calc μ {ω | A false ω = true ∧ B false ω = true}
      ≤ μ ({ω | A false ω = true ∧ B true ω = false} ∪
          ({ω | A true ω = false ∧ B false ω = true} ∪
            {ω | A true ω = true ∧ B true ω = true})) := measure_mono hsub
    _ ≤ μ {ω | A false ω = true ∧ B true ω = false} +
          (μ {ω | A true ω = false ∧ B false ω = true} +
            μ {ω | A true ω = true ∧ B true ω = true}) :=
        le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)
    _ = 0 := by rw [hA₁B₂, hA₂B₁, hA₂B₂]; simp

/-! ## A quantum model realising the Hardy conditions

We exhibit an explicit two-qubit state and explicit projective measurements for which the
Hardy conditions hold, with the "paradoxical" event occurring in a fraction `1/12` of the
runs.  Combined with `QI.hardy_paradox`, this shows that the quantum predictions cannot be
reproduced by any local hidden-variable model — and, unlike Bell's theorem, the argument uses
no inequalities, only events of probability zero and one event of positive probability.

The state is `ψ = (|01⟩ + |10⟩ - |11⟩)/√3`.  For setting `true` (the second measurement) each
party measures in the computational basis; for setting `false` (the first measurement) each
party measures in the basis `(|0⟩ ± |1⟩)/√2`, with the outcome `1` corresponding to `+`. -/

/-- The measurement vector of a party for setting `x` and outcome `a` (a unit vector in `ℂ²`).
For each fixed setting the two outcome vectors form an orthonormal basis of `ℂ²`. -/
