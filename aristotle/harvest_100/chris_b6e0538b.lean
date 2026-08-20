/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring `/-! ... -/` before `import`, so the required
-- header above is written as an ordinary block comment with identical text.)

import Mathlib

namespace Math

/-- **Key intermediate lemma.** If a prime `p` divides the order of a finite group `G`, then `G`
contains a nontrivial element `x` killed by `p`, i.e. `x ≠ 1` and `x ^ p = 1`. -/
theorem exists_ne_one_pow_prime_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card G) : ∃ x : G, x ≠ 1 ∧ x ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdvd
  refine ⟨x, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · rw [← hx]
    exact pow_orderOf_eq_one x

/-- An element `x ≠ 1` of a group with `x ^ p = 1`, for `p` prime, has order exactly `p`. -/
theorem orderOf_eq_of_prime_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {x : G} (hx : x ≠ 1) (hxp : x ^ p = 1) : orderOf x = p := by
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx
  · exact h

/-- **Cauchy's theorem.** If a prime `p` divides the order of a finite group `G`, then `G` has an
element of order `p`. -/
theorem cauchy_group {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
  obtain ⟨x, hx1, hxp⟩ := exists_ne_one_pow_prime_eq_one hp hdvd
  exact ⟨x, orderOf_eq_of_prime_pow_eq_one hp hx1 hxp⟩

end Math

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

