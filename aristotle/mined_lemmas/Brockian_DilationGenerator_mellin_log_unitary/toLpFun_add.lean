import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` as an identity of Lebesgue (`ℝ≥0∞`-valued) integrals:
integrating over `(0, ∞)` is the same as integrating `exp t • ·` over all of `ℝ`. -/

lemma toLpFun_add (f g : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLpFun (f + g) = toLpFun f + toLpFun g := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_toLpFun (f + g), coeFn_toLpFun f, coeFn_toLpFun g,
    Lp.coeFn_add (toLpFun f) (toLpFun g), mellinLog_congr_ae (Lp.coeFn_add f g)]
    with t h1 h2 h3 h4 h5
  rw [h1, h4, h5, mellinLog_add]
  simp [h2, h3]

