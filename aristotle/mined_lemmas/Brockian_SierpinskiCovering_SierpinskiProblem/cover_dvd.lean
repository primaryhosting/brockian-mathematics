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
/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is wrapped in a plain block comment because Lean 4 requires
-- `import` commands to precede every other command, including module docstrings.)

import Mathlib

set_option maxHeartbeats 4000000

namespace Brockian.SierpinskiCovering

/-- `k` is a *Sierpiński number*: an odd positive integer `k` such that `k * 2 ^ n + 1`
is composite for every `n ≥ 1`. -/

theorem cover_dvd (n : ℕ) : cover n ∣ 78557 * 2 ^ n + 1 := by
  obtain ⟨hlt, -, hdvd, hper⟩ := cover_spec (n % 36) (Nat.mod_lt _ (by norm_num))
  set p := coverList.getD (n % 36) 1 with hpdef
  have hcov : cover n = p := rfl
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hlt
  have h2 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [hper, hone]
  have h3 : ((2 : ℕ) ^ 36) ^ (n / 36) ≡ 1 [MOD p] := by
    simpa using h2.pow (n / 36)
  have hsplit : (2 : ℕ) ^ n = ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ (n % 36) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h4 : (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD p] := by
    rw [hsplit]
    simpa using h3.mul_right ((2 : ℕ) ^ (n % 36))
  have h5 : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD p] :=
    (h4.mul_left 78557).add_right 1
  have h6 : 78557 * 2 ^ (n % 36) + 1 ≡ 0 [MOD p] := by
    unfold Nat.ModEq
    simpa using hdvd
  rw [hcov]
  exact Nat.modEq_zero_iff_dvd.1 (h5.trans h6)

/-- **The Sierpiński covering theorem.** `78557` is a Sierpiński number: `78557 * 2 ^ n + 1`
is composite for every `n ≥ 1`, because it is always divisible by one of the primes of the
covering set `{3, 5, 7, 13, 19, 37, 73}`.

(That `78557` is the *smallest* Sierpiński number is the still-open Sierpiński problem;
what is proved here is the covering half of it.) -/
