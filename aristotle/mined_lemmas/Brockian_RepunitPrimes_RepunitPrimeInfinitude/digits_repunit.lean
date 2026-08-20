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

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th base-ten repunit `R n = 1 + 10 + ⋯ + 10 ^ (n - 1)`, i.e. the natural number
whose decimal expansion consists of `n` ones. -/

theorem digits_repunit (n : ℕ) : Nat.digits 10 (repunit n) = List.replicate n 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < repunit (n + 1) := by
        rw [repunit_succ']; omega
      rw [Nat.digits_def' (by norm_num) hpos, repunit_succ']
      have h1 : (10 * repunit n + 1) % 10 = 1 := by omega
      have h2 : (10 * repunit n + 1) / 10 = repunit n := by omega
      rw [h1, h2, ih, List.replicate_succ]

