import Mathlib

/-!
# Square Ray Primes Mod 20
Category: Cone Line
Target: Brockian.ConeLine.square_ray_primes_mod20
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

/-- **Square ray primes mod 20.** A prime `p > 5` with `p ≡ 1` or `p ≡ 4 (mod 5)` satisfies
`p % 20 ∈ {1, 9, 11, 19}`.

Proof: such a `p` is odd, and the pair `(p % 2, p % 5)` determines `p % 10`, hence `p % 20`
is constrained to the four listed residues. -/
theorem square_ray_primes_mod20 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 < p)
    (h : p % 5 = 1 ∨ p % 5 = 4) :
    p % 20 = 1 ∨ p % 20 = 9 ∨ p % 20 = 11 ∨ p % 20 = 19 := by
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    rcases Nat.Prime.eq_one_or_self_of_dvd hp 2 hd with h' | h' <;> omega
  have hodd : p % 2 = 1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h2
    omega
  omega

end Brockian.ConeLine

