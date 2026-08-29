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
theorem five_not_dvd_of_prime_gt_five {n : ℕ} (hn : Nat.Prime n) (h : 5 < n) :
    ¬ (5 ∣ n) := by
  intro hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h2
  · omega
  · omega

/--
**Cousin prime roads.** If `p` and `p + 4` are both prime and `p > 5`, then on the
five-ray wheel the pair `(p % 5, (p+4) % 5)` is exactly one of the roads
`2 → 1`, `3 → 2`, `4 → 3`.
-/
theorem cousin_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 4))
    (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have hp5 : ¬ (5 ∣ p) := five_not_dvd_of_prime_gt_five hp h5
  have hq5 : ¬ (5 ∣ (p + 4)) := five_not_dvd_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at hp5 hq5
  have h1 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h2 : (p + 4) % 5 = (p % 5 + 4) % 5 := by
    omega
  simp only [Prod.mk.injEq]
  interval_cases h : (p % 5) <;> omega

end ConeLine
end Brockian

