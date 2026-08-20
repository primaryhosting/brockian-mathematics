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

/-- A Sophie Germain prime `p > 5` never has residue `2` modulo `5`, and the pair of
residues `(p % 5, (2 * p + 1) % 5)` is one of `(1, 3)`, `(3, 2)`, `(4, 4)`. -/
theorem sophie_germain_avoids_ray2 (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (2 * p + 1))
    (h5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hp5 : ¬ (5 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h
    omega
  have hq5 : ¬ (5 ∣ (2 * p + 1)) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).1 h
    omega
  have hp5' : p % 5 ≠ 0 := fun h => hp5 (Nat.dvd_of_mod_eq_zero h)
  have hq5' : (2 * p + 1) % 5 ≠ 0 := fun h => hq5 (Nat.dvd_of_mod_eq_zero h)
  refine ⟨by omega, ?_⟩
  have : p % 5 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases this with h | h | h
  · exact Or.inl (by simp [Prod.ext_iff]; omega)
  · exact Or.inr (Or.inl (by simp [Prod.ext_iff]; omega))
  · exact Or.inr (Or.inr (by simp [Prod.ext_iff]; omega))

end Brockian.ConeLine

