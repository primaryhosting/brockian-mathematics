import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.ConeLine

/-- A prime greater than `5` is not divisible by `5`. -/
lemma not_dvd_five_of_prime_gt_five {n : ℕ} (hn : n.Prime) (h : 5 < n) : ¬ (5 ∣ n) := by
  intro hdvd
  have : (5 : ℕ) = 1 ∨ (5 : ℕ) = n := hn.eq_one_or_self_of_dvd 5 hdvd
  omega

/-- **Sexy prime roads.** If `p` and `p + 6` are both prime and `p > 5`, then the pair of
residues `(p % 5, (p + 6) % 5)` is one of `(1, 2)`, `(2, 3)`, `(3, 4)`; i.e. sexy primes travel
exactly the roads `1 → 2`, `2 → 3`, `3 → 4`, and neither endpoint sits on ray `0`. -/
theorem sexy_prime_roads (p : ℕ) (hp : p.Prime) (hq : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have hp5 : ¬ (5 ∣ p) := not_dvd_five_of_prime_gt_five hp h5
  have hq5 : ¬ (5 ∣ (p + 6)) := not_dvd_five_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at hp5 hq5
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

