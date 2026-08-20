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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to appear before any other syntax,
so the mandated header block is placed immediately after the single `import Mathlib` line.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd d (n / d) = 1`. -/

theorem fiveUnitaryPerfectExist :
    ∃ S : Finset ℕ, S.card = 5 ∧ ∀ n ∈ S, IsUnitaryPerfect n :=
  ⟨knownUnitaryPerfect, card_knownUnitaryPerfect, fun _ hn => unitaryPerfect_of_mem_known hn⟩

/-! ## The sixth unitary perfect number

Whether a sixth unitary perfect number exists is a well-known open problem, so the statement
below is a *conditional reduction*: the existence of six unitary perfect numbers is proved
from (and in fact is equivalent to) the existence of a single unitary perfect number outside
the classically known list of five. -/

/-- **Conditional reduction.** If some unitary perfect number lies outside the classically known
list of five, then there are six unitary perfect numbers, i.e. a sixth unitary perfect number
exists. (Unconditional existence of a sixth unitary perfect number is an open problem.) -/
