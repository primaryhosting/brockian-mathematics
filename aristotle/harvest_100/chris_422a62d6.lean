/-!
# Gcd
Category: Fibonacci
Target: Fibonacci.gcd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean does not allow any command (including a module
docstring `/-! ... -/`) to precede the `import` lines of a file, so this file,
which must begin with the header comment above, carries no imports and develops
the statement from the Lean core library alone.  The companion file
`RequestProject/GcdMathlib.lean` imports Mathlib, checks that the Fibonacci
function defined here agrees with Mathlib's `Nat.fib`, and records the literal
Mathlib statement `Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n)`
(proved via `Nat.fib_gcd`).
-/

namespace Fibonacci

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This is the same function as Mathlib's `Nat.fib`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

@[simp] theorem fib_zero : fib 0 = 0 := rfl

@[simp] theorem fib_one : fib 1 = 1 := rfl

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- Auxiliary two-component statement used to prove the addition formula. -/
theorem fib_add_aux (m k : Nat) :
    fib (m + k + 1) = fib m * fib k + fib (m + 1) * fib (k + 1) ∧
      fib (m + k + 2) = fib m * fib (k + 1) + fib (m + 1) * fib (k + 2) := by
  induction k with
  | zero =>
    constructor
    · simp
    · rw [fib_add_two m]
      simp [fib_add_two 0]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : fib (m + k + 3) = fib (m + k + 1) + fib (m + k + 2) := fib_add_two (m + k + 1)
    have hk : fib (k + 3) = fib (k + 1) + fib (k + 2) := fib_add_two (k + 1)
    constructor
    · show fib (m + k + 2) = _
      rw [ih2]
    · show fib (m + k + 3) = fib m * fib (k + 2) + fib (m + 1) * fib (k + 3)
      rw [hstep, ih1, ih2, hk, fib_add_two k]
      simp [Nat.mul_add]
      omega

/-- The Fibonacci addition formula. -/
theorem fib_add (m k : Nat) :
    fib (m + k + 1) = fib m * fib k + fib (m + 1) * fib (k + 1) :=
  (fib_add_aux m k).1

/-- Consecutive Fibonacci numbers are coprime. -/
theorem fib_coprime_fib_succ (n : Nat) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => decide
  | succ k ih =>
    show Nat.gcd (fib (k + 1)) (fib (k + 2)) = 1
    rw [fib_add_two k, Nat.gcd_add_self_right]
    rw [Nat.gcd_comm]
    exact ih

theorem gcd_fib_add_self (m n : Nat) :
    Nat.gcd (fib m) (fib (n + m)) = Nat.gcd (fib m) (fib n) := by
  cases m with
  | zero => simp
  | succ k =>
    have hsum : n + (k + 1) = n + k + 1 := by omega
    rw [hsum, fib_add n k, Nat.gcd_add_mul_right_right,
      (fib_coprime_fib_succ k).gcd_mul_right_cancel_right (fib n)]

theorem gcd_fib_add_mul_self (m n k : Nat) :
    Nat.gcd (fib m) (fib (n + m * k)) = Nat.gcd (fib m) (fib n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : n + m * (k + 1) = (n + m * k) + m := by
      rw [Nat.mul_succ]; omega
    rw [h, gcd_fib_add_self, ih]

/-- **Fibonacci-gcd**: `fib (gcd m n) = gcd (fib m) (fib n)` for all naturals `m n`. -/
theorem gcd (m n : Nat) : fib (Nat.gcd m n) = Nat.gcd (fib m) (fib n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp
  | H1 m n hm ih =>
    rw [← Nat.gcd_rec m n] at ih
    have key : Nat.gcd (fib m) (fib (n % m + m * (n / m))) = Nat.gcd (fib m) (fib (n % m)) :=
      gcd_fib_add_mul_self m (n % m) (n / m)
    rw [Nat.mod_add_div] at key
    rw [ih, Nat.gcd_comm (fib (n % m)) (fib m), key]

end Fibonacci

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
import RequestProject.Gcd

/-!
# Gcd (Mathlib form)

Companion to `RequestProject/Gcd.lean`.  Here we import Mathlib, check that
`Fibonacci.fib` is Mathlib's `Nat.fib`, and record the statement in Mathlib
terms, proved via `Nat.fib_gcd`.
-/

namespace Fibonacci

/-- The Fibonacci function of `RequestProject/Gcd.lean` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (k + 2) =>
      rw [fib_add_two, Nat.fib_add_two, ih k (by omega), ih (k + 1) (by omega)]

/-- **Fibonacci-gcd** in Mathlib terms:
`Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n)`. -/
theorem nat_fib_gcd (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n

end Fibonacci

