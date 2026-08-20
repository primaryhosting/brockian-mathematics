/-
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
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

namespace Math

/-- **Fermat's little theorem.** If `p` is prime and `p` does not divide the integer `a`,
then `a ^ (p - 1) ≡ 1 (mod p)`. -/
theorem fermat_little {p : ℕ} (hp : Nat.Prime p) {a : ℤ} (ha : ¬ ((p : ℤ) ∣ a)) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hnd : ¬ (p ∣ a.natAbs) := fun h =>
    ha (Int.natAbs_dvd_natAbs.mp (by simpa using h))
  have hcop : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime p a.natAbs := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using h1
  exact Int.ModEq.pow_card_sub_one_eq_one hp hcop

end Math

