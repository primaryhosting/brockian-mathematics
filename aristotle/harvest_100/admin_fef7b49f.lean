/-
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: verified (axiom-clean; propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: verified (axiom-clean; propext, Classical.choice, Quot.sound)
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

/-- A prime `q` with `5 < q` is not divisible by `5`.
Uses `Nat.prime_dvd_prime_iff_eq` from Mathlib. -/
theorem not_five_dvd_of_prime_gt_five {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) : ¬ (5 ∣ q) := by
  intro hdvd
  have : (5 : ℕ) = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/--
**Sophie Germain primes avoid ray 2.**

If `p > 5` is a Sophie Germain prime (both `p` and `2p+1` prime), then `p % 5 ≠ 2`
(otherwise `5 ∣ 2p+1`), and the pair of residues `(p % 5, (2p+1) % 5)` is one of
`(1,3)`, `(3,2)`, `(4,4)`.
-/
theorem sophie_germain_avoids_ray2 {p : ℕ} (hp : p.Prime) (hq : (2 * p + 1).Prime)
    (hgt : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨
       (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
       (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hp5 : ¬ (5 ∣ p) := not_five_dvd_of_prime_gt_five hp hgt
  have hq5 : ¬ (5 ∣ (2 * p + 1)) :=
    not_five_dvd_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at hp5 hq5
  refine ⟨by omega, ?_⟩
  have hr : p % 5 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  simp only [Prod.mk.injEq]
  rcases hr with hr | hr | hr
  · exact Or.inl ⟨hr, by omega⟩
  · exact Or.inr (Or.inl ⟨hr, by omega⟩)
  · exact Or.inr (Or.inr ⟨hr, by omega⟩)

end Brockian.ConeLine

