/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Statement: A Sophie Germain prime p > 5 (p and 2p+1 both prime) never sits on ray 2: p ≡ 2 (mod 5) would force 5 ∣ 2p+1. Its roads are 1→3, 3→2, 4→4 — ray 4 maps to itself.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

namespace Brockian.ConeLine

/-- A Sophie Germain prime `p > 5` (both `p` and `2p+1` prime) never has residue `2` mod `5`,
and the pair of residues `(p % 5, (2p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/
theorem sophie_germain_avoids_ray2 {p : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime (2 * p + 1))
    (hp5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have h5 : Nat.Prime 5 := by norm_num
  have hpd : ¬ (5 ∣ p) := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq h5 hp).mp h
    omega
  have hqd : ¬ (5 ∣ (2 * p + 1)) := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq h5 hq).mp h
    omega
  rw [Nat.dvd_iff_mod_eq_zero] at hpd hqd
  obtain ⟨k, hk⟩ : ∃ k, p = 5 * k + p % 5 := ⟨p / 5, by omega⟩
  have hr : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases hr with h0 | h0 | h0 | h0 <;> rw [h0] at hk <;> subst hk <;>
    simp [Nat.add_mod, Nat.mul_mod, h0] at hqd ⊢

end Brockian.ConeLine

