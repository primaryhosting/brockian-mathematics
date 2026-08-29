import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series
is non-zero) when for every prime `p` the elements of `H` omit at least one
residue class modulo `p`. -/

theorem card_factorialTuple (k : ℕ) : (factorialTuple k).card = k := by
  have hinj : Function.Injective (fun i : ℕ => i * k !) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) hab
  rw [factorialTuple, Finset.card_image_of_injective _ hinj, Finset.card_range]

