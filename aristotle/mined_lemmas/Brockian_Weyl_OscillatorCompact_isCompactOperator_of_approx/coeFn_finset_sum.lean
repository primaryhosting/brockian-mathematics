/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → L2R) :
    ⇑(∑ i ∈ s, F i) =ᵐ[volume] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
  | insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
      show (⇑(∑ i ∈ insert a s, F i)) x = _
      rw [Finset.sum_insert ha, Finset.sum_insert ha, h1]
      simp only [Pi.add_apply, h2]

