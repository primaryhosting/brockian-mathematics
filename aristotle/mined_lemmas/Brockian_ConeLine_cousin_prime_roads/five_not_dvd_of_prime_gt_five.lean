/-
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace ConeLine

/-- A prime `n` greater than `5` is not divisible by `5`. -/

theorem five_not_dvd_of_prime_gt_five {n : ℕ} (hn : n.Prime) (h : 5 < n) : n % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h2
  · omega
  · omega

/-- Cousin primes `(p, p+4)` with `p > 5` travel exactly the roads
`2 → 1`, `3 → 2`, `4 → 3` on the five-ray wheel. -/
