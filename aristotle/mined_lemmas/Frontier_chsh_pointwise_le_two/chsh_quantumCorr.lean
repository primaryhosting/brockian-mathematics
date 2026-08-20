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

theorem chsh_quantumCorr : chsh quantumCorr = 2 * Real.sqrt 2 := by
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h34 : Real.cos (Real.pi / 2 - -(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
    have : Real.pi / 2 - -(Real.pi / 4) = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, h4]
  have hneg : Real.cos (0 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [zero_sub, Real.cos_neg, h4]
  have h2 : Real.cos (0 - -(Real.pi / 4)) = Real.sqrt 2 / 2 := by
    have : (0 : ℝ) - -(Real.pi / 4) = Real.pi / 4 := by ring
    rw [this, h4]
  have h3 : Real.cos (Real.pi / 2 - Real.pi / 4) = Real.sqrt 2 / 2 := by
    have : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [this, h4]
  simp only [chsh, quantumCorr, angleA, angleB, if_true, if_false, Bool.false_eq_true]
  rw [hneg, h2, h3, h34]
  ring

/-- **Bell's theorem**: no local hidden-variable model reproduces the quantum correlations.

Indeed, every local hidden-variable model obeys the CHSH inequality `CHSH ≤ 2`
(`Frontier.chsh_le_two`), whereas the quantum correlations achieve `CHSH = 2√2 > 2`. -/
