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
## Setting

Hardy's nonlocality argument.  Two spacelike separated parties, Alice and Bob, each
choose one of two measurement settings and record a `Bool` outcome.  A *local
hidden-variable* (local realistic) model consists of

* a space `Λ` of hidden variables carrying a probability measure `μ`,
* response functions `a₁, a₂ : Λ → Bool` for Alice's two settings and
  `b₁, b₂ : Λ → Bool` for Bob's two settings,

Alice's outcome depending only on her own setting and on `λ`, and likewise for Bob
(this is exactly locality plus outcome determinism; the functions are *not* assumed
measurable, all statements are about the outer measure `μ`).

The four *Hardy conditions* are

* `μ {λ | a₂ λ ∧ b₂ λ} > 0`  (the "Hardy event" happens in a nonzero fraction of runs),
* `μ {λ | a₁ λ ∧ b₂ λ} = 0`,
* `μ {λ | a₂ λ ∧ b₁ λ} = 0`,
* `μ {λ | ¬ a₁ λ ∧ ¬ b₁ λ} = 0`.

Hardy's argument shows these four are jointly contradictory: no inequality is needed,
a single run of the Hardy event already refutes local realism.
-/

section LocalModel

variable {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ) (a₁ a₂ b₁ b₂ : Λ → Bool)

/-- The "Hardy event": Alice's second setting and Bob's second setting both yield `true`. -/
def hardyEvent : Set Λ := {l | a₂ l = true ∧ b₂ l = true}

omit [MeasurableSpace Λ] in
/-- Pointwise core of Hardy's argument: on any hidden variable in the Hardy event, at
least one of the three events that Hardy's conditions declare impossible must occur. -/
theorem hardyEvent_subset :
    hardyEvent a₂ b₂ ⊆
      {l | a₁ l = true ∧ b₂ l = true} ∪
      {l | a₂ l = true ∧ b₁ l = true} ∪
      {l | a₁ l = false ∧ b₁ l = false} := by
  rintro l ⟨h2, h2'⟩
  by_cases ha : a₁ l = true
  · exact Or.inl (Or.inl ⟨ha, h2'⟩)
  · by_cases hb : b₁ l = true
    · exact Or.inl (Or.inr ⟨h2, hb⟩)
    · exact Or.inr ⟨by simpa using ha, by simpa using hb⟩

/-- **Hardy's inequality for local hidden-variable models.**  In any local realistic
model the probability of the Hardy event is bounded by the sum of the probabilities of
the three events that quantum mechanics predicts to be impossible.  In particular, if
those three have probability zero, so has the Hardy event. -/
theorem hardy_local_bound :
    μ (hardyEvent a₂ b₂) ≤
      μ {l | a₁ l = true ∧ b₂ l = true} +
      μ {l | a₂ l = true ∧ b₁ l = true} +
      μ {l | a₁ l = false ∧ b₁ l = false} := by
  refine le_trans (measure_mono (hardyEvent_subset a₁ a₂ b₁ b₂)) ?_
  exact le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)

/-- **Hardy's paradox.**  No local hidden-variable model can reproduce the four Hardy
conditions: if the three "impossible" events have probability zero, then the Hardy
event has probability zero as well, so it cannot occur in a nonzero fraction of runs.
Hence a nonzero fraction of runs witnesses the violation of local realism, with no
inequality (no statistical Bell-type argument) involved. -/
theorem hardy_paradox
    (h₁₂ : μ {l | a₁ l = true ∧ b₂ l = true} = 0)
    (h₂₁ : μ {l | a₂ l = true ∧ b₁ l = true} = 0)
    (h₁₁ : μ {l | a₁ l = false ∧ b₁ l = false} = 0)
    (hpos : 0 < μ (hardyEvent a₂ b₂)) : False := by
  have h := hardy_local_bound μ a₁ a₂ b₁ b₂
  rw [h₁₂, h₂₁, h₁₁] at h
  simp only [add_zero, nonpos_iff_eq_zero] at h
  exact absurd h hpos.ne'

end LocalModel

/-!
## Non-vacuity: a no-signalling box satisfying Hardy's conditions

The four Hardy conditions are contradictory only under *locality*.  To see that they are
not contradictory per se, we exhibit an explicit no-signalling behaviour
`hardyBox x y a b = P(a, b | x, y)` (settings `x, y : Bool`, outcomes `a, b : Bool`)
which satisfies the three vanishing conditions while the Hardy event has probability
`1 / 2`.
-/

/-- An explicit no-signalling box satisfying Hardy's conditions with Hardy fraction `1/2`.
Here `x`, `y` are Alice's and Bob's settings and `a`, `b` their outcomes. -/
def hardyBox : Bool → Bool → Bool → Bool → ℚ
  | false, false, a, b => if a = b then 0 else 1 / 2
  | false, true,  a, b => if a = b then 0 else 1 / 2
  | true,  false, a, b => if a = b then 0 else 1 / 2
  | true,  true,  a, b => if a = b then 1 / 2 else 0

theorem hardyBox_nonneg (x y a b : Bool) : 0 ≤ hardyBox x y a b := by
  cases x <;> cases y <;> cases a <;> cases b <;> norm_num [hardyBox]

theorem hardyBox_normalized (x y : Bool) :
    ∑ a : Bool, ∑ b : Bool, hardyBox x y a b = 1 := by
  cases x <;> cases y <;> norm_num [hardyBox, Fintype.sum_bool]

/-- No-signalling from Bob to Alice: Alice's marginal does not depend on Bob's setting. -/
theorem hardyBox_no_signalling_left (x a : Bool) :
    ∑ b : Bool, hardyBox x false a b = ∑ b : Bool, hardyBox x true a b := by
  cases x <;> cases a <;> norm_num [hardyBox, Fintype.sum_bool]

/-- No-signalling from Alice to Bob: Bob's marginal does not depend on Alice's setting. -/
theorem hardyBox_no_signalling_right (y b : Bool) :
    ∑ a : Bool, hardyBox false y a b = ∑ a : Bool, hardyBox true y a b := by
  cases y <;> cases b <;> norm_num [hardyBox, Fintype.sum_bool]

/-- The box satisfies the three vanishing Hardy conditions, and the Hardy event has
probability `1/2`; so the Hardy conditions are consistent for a general (nonlocal)
no-signalling behaviour, even though `QI.hardy_paradox` shows they are inconsistent for
every local hidden-variable model. -/
theorem hardyBox_hardy_conditions :
    hardyBox false true true true = 0 ∧
    hardyBox true false true true = 0 ∧
    hardyBox false false false false = 0 ∧
    hardyBox true true true true = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hardyBox]

end QI

