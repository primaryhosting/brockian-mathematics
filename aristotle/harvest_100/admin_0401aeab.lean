/-
# Instance 1000
Category: Frontier — Prime Numbers
Target: Goldbach.instance_1000
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- NOTE: the requested header is reproduced above as a plain block comment: Lean 4
-- requires `import` commands to be the first commands in a file, and a `/-! ... -/`
-- module docstring at the very top would make `import Mathlib` illegal.

import Mathlib

namespace Goldbach

/-- **Goldbach instance for 1000.** `1000` is a sum of two primes: `3 + 997`.

The primality facts are decided by `Nat.Prime`'s decidability instance
(`Nat.decidablePrime`), invoked through `norm_num`'s `Nat.Prime` extension. -/
theorem instance_1000 : Nat.Prime 3 ∧ Nat.Prime 997 ∧ 3 + 997 = 1000 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-- The same instance phrased as an existence statement:
there are primes `p, q` with `p + q = 1000`. -/
theorem exists_primes_add_eq_1000 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 1000 :=
  ⟨3, 997, instance_1000.1, instance_1000.2.1, instance_1000.2.2⟩

end Goldbach

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

