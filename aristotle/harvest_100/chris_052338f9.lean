import Mathlib

/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
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

/-- A Sophie Germain prime `p > 5` (both `p` and `2p+1` prime) never has residue `2` mod `5`,
and the pair of residues `(p % 5, (2p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/
theorem sophie_germain_avoids_ray2 (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (2 * p + 1))
    (h5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hnp : ¬ (5 ∣ p) := by
    intro h
    rcases (hp.eq_one_or_self_of_dvd 5 h) with h' | h' <;> omega
  have hnq : ¬ (5 ∣ (2 * p + 1)) := by
    intro h
    rcases (hq.eq_one_or_self_of_dvd 5 h) with h' | h' <;> omega
  rw [Nat.dvd_iff_mod_eq_zero] at hnp hnq
  have key : (2 * p + 1) % 5 = (2 * (p % 5) + 1) % 5 := by
    simp [Nat.add_mod, Nat.mul_mod]
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (p % 5) <;> simp_all

end Brockian.ConeLine

#print axioms Brockian.ConeLine.sophie_germain_avoids_ray2

