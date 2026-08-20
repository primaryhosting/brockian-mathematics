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

theorem chsh_le_two (M : LHVModel) : chsh M.corr ≤ 2 := by
  have hsum : chsh M.corr =
      ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
            + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ := by
    have s1 := integral_add (M.integrable_prod false false) (M.integrable_prod false true)
    have s2 := integral_add ((M.integrable_prod false false).add (M.integrable_prod false true))
      (M.integrable_prod true false)
    have s3 := integral_sub (((M.integrable_prod false false).add
      (M.integrable_prod false true)).add (M.integrable_prod true false))
      (M.integrable_prod true true)
    simp only [Pi.add_apply] at s2 s3
    rw [s3, s2, s1]
    rfl
  rw [hsum]
  have hint : Integrable (fun x => M.A false x * M.B false x + M.A false x * M.B true x
      + M.A true x * M.B false x - M.A true x * M.B true x) M.μ :=
    (((M.integrable_prod false false).add (M.integrable_prod false true)).add
      (M.integrable_prod true false)).sub (M.integrable_prod true true)
  have hle : ∫ x, (M.A false x * M.B false x + M.A false x * M.B true x
      + M.A true x * M.B false x - M.A true x * M.B true x) ∂M.μ
      ≤ ∫ _x, (2 : ℝ) ∂M.μ := by
    refine integral_mono hint (integrable_const 2) (fun x => ?_)
    exact chsh_pointwise_le_two _ _ _ _ (M.boundA false x) (M.boundA true x)
      (M.boundB false x) (M.boundB true x)
  simpa using hle

/-- A deterministic local hidden-variable model achieving the CHSH value `2`:
Alice always outputs `+1`, and Bob outputs `+1` for his first setting and `-1` for the second.
In particular local hidden-variable models exist, so `Frontier.bell_theorem` is not vacuous,
and the bound in `Frontier.chsh_le_two` is sharp. -/
