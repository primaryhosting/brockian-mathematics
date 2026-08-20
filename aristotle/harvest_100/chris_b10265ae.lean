import Mathlib

/-!
# Pair 11 13
Category: Frontier — Prime Numbers
Target: Twin.pair_11_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the header comment above had to be placed after `import Mathlib`, since Lean 4
-- requires all `import` commands to precede any other syntax (including module docstrings).

namespace Twin

/-- `11` and `13` are twin primes: both are prime and their difference is `2`.

Primality of `11` is the existing Mathlib lemma `Nat.prime_eleven`; Mathlib has no
`Nat.prime_thirteen`, so primality of `13` is discharged by the `norm_num` primality
extension (equivalently `decide`). -/
theorem pair_11_13 : Nat.Prime 11 ∧ Nat.Prime 13 ∧ 13 - 11 = 2 :=
  ⟨Nat.prime_eleven, by norm_num, rfl⟩

end Twin

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

