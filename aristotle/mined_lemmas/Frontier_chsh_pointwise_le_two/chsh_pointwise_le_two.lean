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

namespace Frontier

open MeasureTheory

/-- A **local hidden-variable model** for a two-party, two-setting, ±1-outcome experiment.

A hidden variable `x` is drawn from a probability space `(Λ, μ)`.  Alice's outcome
`A a x` depends only on her setting `a : Bool` and on the hidden variable, and likewise
Bob's outcome `B b x` depends only on his setting `b : Bool` and on the hidden variable
(this is the *locality* assumption).  Outcomes are bounded by `1` in absolute value. -/
structure LHVModel where
  /-- The space of hidden variables. -/
  Λ : Type
  /-- The measurable structure on the hidden-variable space. -/
  mΛ : MeasurableSpace Λ
  /-- The distribution of the hidden variable. -/
  μ : Measure Λ
  /-- The hidden variable is distributed according to a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- Alice's outcome as a function of her setting and the hidden variable. -/
  A : Bool → Λ → ℝ
  /-- Bob's outcome as a function of his setting and the hidden variable. -/
  B : Bool → Λ → ℝ
  measA : ∀ a, Measurable (A a)
  measB : ∀ b, Measurable (B b)
  boundA : ∀ a x, |A a x| ≤ 1
  boundB : ∀ b x, |B b x| ≤ 1

attribute [instance] LHVModel.mΛ LHVModel.prob

/-- The correlation predicted by a local hidden-variable model for settings `a`, `b`:
the expectation of the product of the two outcomes. -/

theorem chsh_pointwise_le_two (a0 a1 b0 b1 : ℝ) (h0 : |a0| ≤ 1) (h1 : |a1| ≤ 1)
    (g0 : |b0| ≤ 1) (g1 : |b1| ≤ 1) :
    a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 ≤ 2 := by
  have e0 : a0 * (b0 + b1) ≤ |b0 + b1| := by
    calc a0 * (b0 + b1) ≤ |a0 * (b0 + b1)| := le_abs_self _
      _ = |a0| * |b0 + b1| := abs_mul _ _
      _ ≤ 1 * |b0 + b1| := by gcongr
      _ = |b0 + b1| := one_mul _
  have e1 : a1 * (b0 - b1) ≤ |b0 - b1| := by
    calc a1 * (b0 - b1) ≤ |a1 * (b0 - b1)| := le_abs_self _
      _ = |a1| * |b0 - b1| := abs_mul _ _
      _ ≤ 1 * |b0 - b1| := by gcongr
      _ = |b0 - b1| := one_mul _
  rcases abs_cases (b0 + b1) with ⟨p1, _⟩ | ⟨p1, _⟩ <;>
    rcases abs_cases (b0 - b1) with ⟨p2, _⟩ | ⟨p2, _⟩ <;>
      rw [abs_le] at g0 g1 <;> nlinarith [e0, e1]

/-- Products of outcomes are integrable in any local hidden-variable model. -/
