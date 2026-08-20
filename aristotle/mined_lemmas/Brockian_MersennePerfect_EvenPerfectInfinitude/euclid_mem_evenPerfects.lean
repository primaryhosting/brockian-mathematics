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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module doc-comment before the import lines, so the
required header appears here as an ordinary block comment; the same text is repeated
as the module docstring immediately after the imports.)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The statement "there are infinitely many even perfect numbers" is open, since it is
equivalent to the (open) conjecture that there are infinitely many Mersenne primes.

What is proved here is exactly that equivalence: a Lean-checked *conditional reduction*
of the infinitude of even perfect numbers to the infinitude of Mersenne primes.

The key input is the Euclid–Euler theorem, already available in Mathlib's Archive as
`Theorems100.Nat.even_and_perfect_iff`
(`Archive/Wiedijk100Theorems/PerfectNumbers.lean`), which states
`Even n ∧ n.Perfect ↔ ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1)`.
-/

namespace Brockian
namespace MersennePerfect

open Nat

/-- The set of even perfect numbers. -/

lemma euclid_mem_evenPerfects {k : ℕ} (hk : k ∈ mersenneExponents) :
    euclid k ∈ evenPerfects :=
  Theorems100.Nat.even_and_perfect_iff.mpr ⟨k, hk, rfl⟩

/-- Euler's direction: every even perfect number is in the image of `euclid`. -/
