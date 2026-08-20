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

set_option grind.warning false

namespace Brockian.ConeLine

/-- A prime `n` greater than `5` is not divisible by `5`. -/

theorem cousin_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 4).Prime) (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have h1 : p % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp h5
  have h2 : (p + 4) % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hq (by omega)
  have h3 : (p + 4) % 5 = (p % 5 + 4) % 5 := by omega
  have h4 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (p % 5) <;> simp_all

end Brockian.ConeLine

