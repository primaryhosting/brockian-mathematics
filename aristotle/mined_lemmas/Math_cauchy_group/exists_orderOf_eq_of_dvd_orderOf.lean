/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import RequestProject.CauchySelfContained

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order `p`.

The proof is self-contained (it does not invoke Mathlib's `exists_prime_orderOf_dvd_card`):
see `Math.cauchy_of_dvd_card`, which argues by strong induction on the order of the group. -/

lemma exists_orderOf_eq_of_dvd_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ} {x : G}
    (h : p ∣ orderOf x) : ∃ g : G, orderOf g = p :=
  ⟨x ^ (orderOf x / p), orderOf_pow_orderOf_div (orderOf_pos x).ne' h⟩

/-- A proper subgroup of a finite group is strictly smaller than the group. -/
