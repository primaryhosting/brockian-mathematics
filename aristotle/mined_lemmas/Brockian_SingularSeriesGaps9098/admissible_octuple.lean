/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set of integers `H` (a "gap pattern") is *admissible* when, for every prime `p`,
the elements of `H` do not cover all residue classes modulo `p`.  This is exactly the condition
under which the associated singular series is nonzero, i.e. the Hardy–Littlewood prime tuple
conjecture predicts infinitely many translates of `H` consisting entirely of primes. -/

theorem admissible_octuple :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ) := by
  apply admissible_of_small_primes
  intro p hp hle
  have hcard : ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℤ).card = 8 := by decide
  rw [hcard] at hle
  have hp2 := hp.two_le
  interval_cases p
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨3, by decide⟩
  · exact absurd hp (by decide)

/-- **Singular Series Gaps 9098.**  New admissible gap ranges: the factorial ladder patterns
`{0, k!, 2·k!, …, (k-1)·k!}` are admissible for every `k`, and every translate of the classical
octuple `{0, 2, 6, 8, 12, 18, 20, 26}` is admissible as well. -/
