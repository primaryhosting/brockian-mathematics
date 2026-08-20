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
# Admissible tuples and positivity of the singular series

An `H : Finset ℕ` (thought of as a set of *gaps* / offsets of a prime constellation
`n + h`, `h ∈ H`) is **admissible** when, for every prime `p`, the reductions of `H`
modulo `p` do not cover all residue classes.  This is exactly the condition under which
the local factors of the Hardy–Littlewood singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^(-|H|)` are all positive.

This file develops the basic theory and a general criterion producing admissible sets:
a set of size at most `m`, all of whose elements are coprime to `m !`, is admissible.
-/

open scoped BigOperators Nat

namespace Brockian

/-- The number of residue classes mod `p` occupied by `H`, i.e. `ν_H(p)`. -/

theorem admissible_coprimeRange {m N : ℕ}
    (hcard : ((Finset.Icc 1 N).filter fun n => Nat.Coprime n (m !)).card ≤ m) :
    Admissible ((Finset.Icc 1 N).filter fun n => Nat.Coprime n (m !)) :=
  admissible_of_coprime_factorial hcard fun _ hn => (Finset.mem_filter.1 hn).2

end Brockian

import RequestProject.Brockian.SingularSeriesGaps

/-!
# A new family of admissible gap ranges inside a window of width `7280`

We exhibit an explicit set `gapSet7280` of `790` natural numbers contained in the interval
`[1, 7280]` and prove that it is admissible, i.e. for every prime `p` the reductions of the
set modulo `p` miss a residue class.  Equivalently every local factor of the
Hardy--Littlewood singular series is positive.

The set is the set of integers in `[1, 7280]` that are coprime to every prime `p ≤ 800`
(namely `1` together with the primes in `(800, 7280]`).  Since it has `790 ≤ 800` elements,
the general criterion `Brockian.admissible_of_coprime_factorial` applies.

Admissibility only depends on the gaps, so *every* translate of this set is admissible as
well; this yields a whole family of admissible gap ranges of width at most `7280`.
-/

open scoped Nat

set_option maxRecDepth 100000

namespace Brockian

/-- The `790` integers in `[1, 7280]` having no prime factor `≤ 800`, listed increasingly. -/
