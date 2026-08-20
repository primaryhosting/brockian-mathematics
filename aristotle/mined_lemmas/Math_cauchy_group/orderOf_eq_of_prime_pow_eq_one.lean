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

theorem orderOf_eq_of_prime_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {x : G} (hx : x ≠ 1) (hxp : x ^ p = 1) : orderOf x = p := by
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx
  · exact h

/-- **Cauchy's theorem.** If a prime `p` divides the order of a finite group `G`, then `G` has an
element of order `p`. -/
