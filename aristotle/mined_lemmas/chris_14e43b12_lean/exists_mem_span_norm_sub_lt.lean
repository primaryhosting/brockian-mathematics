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

import Mathlib

/-!
# Weyl's equidistribution criterion on the additive circle

This file develops equidistribution of sequences on `AddCircle T`.

* `Brockian.Equidistribution.Equidistributed x` says that the empirical averages of a sequence
  `x : ℕ → AddCircle T` converge, against every continuous test function, to the integral of the
  test function with respect to the normalised Haar (probability) measure.
* `Brockian.Equidistribution.WeylSumsVanish x` is the Weyl-sum hypothesis: the empirical averages
  of every nontrivial Fourier monomial `fourier k` (`k ≠ 0`) tend to `0`.
* `Brockian.Equidistribution.equidistribution_of_asymptotic` is the conditional statement
  (Weyl's criterion): `WeylSumsVanish x → Equidistributed x`.
* `Brockian.Equidistribution.weylSumsVanish_rotSeq` discharges the hypothesis for the
  irrational rotation sequence `n ↦ n * a` on `AddCircle 1`, and
  `Brockian.Equidistribution.equidistributed_irrational_rotation` is the resulting unconditional
  equidistribution theorem.
-/

open Filter Topology MeasureTheory AddCircle Complex Submodule Set

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The empirical average of `f` over the first `N` terms of the sequence `x`. -/

lemma exists_mem_span_norm_sub_lt (f : C(AddCircle T, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ span ℂ (range (fourier (T := T))), ‖f - g‖ < ε := by
  have hcl : f ∈ closure ((span ℂ (range (fourier (T := T)))) : Set C(AddCircle T, ℂ)) := by
    show f ∈ (span ℂ (range (fourier (T := T)))).topologicalClosure
    rw [span_fourier_closure_eq_top]; trivial
  rw [Metric.mem_closure_iff] at hcl
  obtain ⟨g, hg, hdist⟩ := hcl ε hε
  exact ⟨g, hg, by rwa [← dist_eq_norm]⟩

/-- **Weyl's criterion**: if all nontrivial Weyl sums of `x` have vanishing averages, then `x`
is equidistributed. -/
