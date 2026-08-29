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

/-
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

lemma monotone_comp_clamp {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) :
    Monotone (fun t => g (clamp t)) := fun _ _ hab =>
  hg (clamp_mem _) (clamp_mem _) (clamp_mono hab)

/-- **Equidistribution for functions of bounded variation.**
If `x` is a uniformly distributed sequence in `[0, 1)` and `f` has bounded variation on `[0, 1]`,
then the Birkhoff averages `(1/N) ∑_{n < N} f (x n)` converge to `∫₀¹ f`. -/
