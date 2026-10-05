import Mathlib
import RequestProject.Math

/-!
# Cassini's identity: companion file

`RequestProject.Math` is required to begin with a fixed header comment, hence it cannot
contain an `import` command and its Fibonacci sequence `Math.fib` is defined from scratch.
Here we import Mathlib and check that `Math.fib` is Mathlib's `Nat.fib`, restate
`Math.cassini_9` in terms of `Nat.fib`, and prove the general Cassini identity.

A search of this Mathlib version turned up no lemma stating Cassini's identity for
`Nat.fib` (only related identities such as `Nat.fib_add_two_sub_fib_add_one` and
`Nat.fib_two_mul_add_one`), so the general statement is proved here by induction.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- **Cassini's identity**: `F n * F (n+2) - F (n+1) ^ 2 = (-1) ^ (n+1)` over `ℤ`. -/
theorem nat_fib_cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have h2 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
      have hpow : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by
        rw [pow_succ]; ring
      rw [show k + 1 + 2 = k + 3 from rfl, h2, hpow, ← ih, h1]
      ring

/-- Cassini's identity at `n = 9`, stated with Mathlib's `Nat.fib`. -/
theorem nat_fib_cassini_9 :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 :=
  nat_fib_cassini 8

/-- The target statement `Math.cassini_9` is exactly Cassini's identity at `n = 8`
for Mathlib's Fibonacci sequence. -/
example :
    (Math.fib 8 : ℤ) * (Math.fib 10 : ℤ) - (Math.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simp only [fib_eq_nat_fib]
  exact nat_fib_cassini_9

end Math

#print axioms Math.cassini_9
#print axioms Math.nat_fib_cassini
#print axioms Math.cassini

/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file must begin with the mandated header comment, so it cannot contain an
`import` line; `Math.fib` is therefore defined here from scratch.  It agrees with
Mathlib's `Nat.fib`, as proved by `Math.fib_eq_nat_fib` in `RequestProject.MathCassini`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity** in general: `F n * F (n+2) - F (n+1) ^ 2 = (-1) ^ (n+1)` over `ℤ`. -/
theorem cassini (n : Nat) :
    (fib n : Int) * (fib (n + 2) : Int) - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
      have h1 : (fib (k + 2) : Int) = (fib k : Int) + (fib (k + 1) : Int) := by
        show ((fib k + fib (k + 1) : Nat) : Int) = _
        omega
      have h2 : (fib (k + 3) : Int) = (fib (k + 1) : Int) + (fib (k + 2) : Int) := by
        show ((fib (k + 1) + fib (k + 2) : Nat) : Int) = _
        omega
      have hpow : ((-1 : Int)) ^ (k + 1 + 1) = -((-1 : Int) ^ (k + 1)) := by
        rw [Int.pow_succ]; omega
      rw [show k + 1 + 2 = k + 3 from rfl, h2, hpow, ← ih, h1]
      grind

/-- **Cassini's identity at `n = 9`**: `F 8 * F 10 - F 9 ^ 2 = (-1) ^ 9`.

Numerically `F 8 = 21`, `F 9 = 34`, `F 10 = 55`, and `21 * 55 - 34 ^ 2 = -1 = (-1) ^ 9`. -/
theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
  decide

end Math

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

