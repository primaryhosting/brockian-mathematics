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
