/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number, spelled out elementarily: `n` is at least `2`
and every divisor of `n` is either `1` or `n`.

This is stated without any `import` because Lean requires every `import` command to
precede all other syntax in a file, including the module docstring above; the file
`RequestProject/Quadruplet11131719Mathlib.lean` proves that `IsPrimeNat` is equivalent
to Mathlib's `Nat.Prime`, and restates the theorem below in those terms. -/

theorem quadruplet_11_13_17_19_nat_prime :
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 := by
  obtain ⟨h11, h13, h17, h19, e1, e2, e3⟩ := quadruplet_11_13_17_19
  exact ⟨(isPrimeNat_iff_nat_prime 11).1 h11, (isPrimeNat_iff_nat_prime 13).1 h13,
    (isPrimeNat_iff_nat_prime 17).1 h17, (isPrimeNat_iff_nat_prime 19).1 h19, e1, e2, e3⟩

end Constellation

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

