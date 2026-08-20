/-
# Instance 1000
Category: Frontier — Prime Numbers
Target: Goldbach.instance_1000
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Instance 1000
Category: Frontier — Prime Numbers
Target: Goldbach.instance_1000
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Goldbach

/-- 1000 is a sum of two primes: `3` and `997`.
Primality of `3` is Mathlib's `Nat.prime_three`; primality of `997` is decided by `norm_num`
(via the `Mathlib.Tactic.NormNum.Prime` extension). -/
theorem instance_1000 : Nat.Prime 3 ∧ Nat.Prime 997 ∧ 3 + 997 = 1000 :=
  ⟨Nat.prime_three, by norm_num, by norm_num⟩

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

