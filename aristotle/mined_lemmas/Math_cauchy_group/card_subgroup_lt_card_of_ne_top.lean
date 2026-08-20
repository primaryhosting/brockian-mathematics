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

lemma card_subgroup_lt_card_of_ne_top {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : H ≠ ⊤) : Nat.card H < Nat.card G := by
  have hd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hne : Nat.card H ≠ Nat.card G := fun he => h (Subgroup.eq_top_of_card_eq H he)
  exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hd) hne

/-- Orbit-stabilizer for the conjugation action: the size of the conjugacy class of `g` times
the order of its centralizer is the order of the group. -/
