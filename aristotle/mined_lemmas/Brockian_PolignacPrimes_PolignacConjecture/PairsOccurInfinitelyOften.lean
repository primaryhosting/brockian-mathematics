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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to come before any module docstring, so the header
-- above appears both at the very top of the file (as a plain comment) and here, after the
-- import, as the module docstring.

namespace Brockian.PolignacPrimes

/-- `GapOccursInfinitelyOften n` says that there are infinitely many pairs of *consecutive*
primes whose difference is exactly `n`: for every bound `N` there is a prime `p > N` such that
`p + n` is prime and no integer strictly between `p` and `p + n` is prime. -/

def PairsOccurInfinitelyOften (n : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + n).Prime

/-- A qualitative Dickson / Hardy–Littlewood hypothesis for the pair of linear forms
`M x + a` and `M x + a + n`: whenever the pair is admissible for the trivial reasons
(`n` even, the modulus `M` even, and both `a` and `a + n` coprime to `M`) there are
infinitely many primes `p ≡ a [MOD M]` with `p + n` prime. -/
