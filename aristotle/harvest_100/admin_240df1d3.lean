/-
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (h5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h1 | h1 <;> omega

/--
A Sophie Germain prime `p > 5` never sits on ray 2: `p % 5 ≠ 2`, and the possible
residue pairs `(p % 5, (2p+1) % 5)` are exactly `(1,3)`, `(3,2)` and `(4,4)`.
-/
theorem sophie_germain_avoids_ray2 {p : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime (2 * p + 1))
    (h5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hp5 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have hq5 : (2 * p + 1) % 5 ≠ 0 := mod_five_ne_zero_of_prime hq (by omega)
  have hmod : (2 * p + 1) % 5 = (2 * (p % 5) + 1) % 5 := by
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.add_mod, Nat.mul_mod]
  refine ⟨?_, ?_⟩ <;>
  · have : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : p % 5 <;> simp_all

end Brockian.ConeLine

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

