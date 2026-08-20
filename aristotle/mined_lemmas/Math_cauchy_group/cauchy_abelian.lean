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

lemma cauchy_abelian {G : Type u} [CommGroup G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) (IH : ∀ m < Nat.card G, p ∣ m → CauchyAt.{u} p m) :
    ∃ g : G, orderOf g = p := by
  have h1 : 1 < Nat.card G := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hdvd)
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  set H := Subgroup.zpowers x with hH
  have hcardH : Nat.card H = orderOf x := Nat.card_zpowers x
  have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have h1' : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hHone : 1 < Nat.card H := by rw [hcardH]; omega
  by_cases hdx : p ∣ orderOf x
  · exact exists_orderOf_eq_of_dvd_orderOf hdx
  · have hmul : Nat.card G = Nat.card (G ⧸ H) * Nat.card H :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H
    have hdq : p ∣ Nat.card (G ⧸ H) := by
      have hpm : p ∣ Nat.card (G ⧸ H) * Nat.card H := hmul ▸ hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hpm with h | h
      · exact h
      · exact absurd (hcardH ▸ h) hdx
    have hqlt : Nat.card (G ⧸ H) < Nat.card G := by
      have := Nat.card_pos (α := G ⧸ H)
      nlinarith [hmul]
    obtain ⟨y', hy'⟩ := IH _ hqlt hdq (G ⧸ H) inferInstance inferInstance rfl
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
    refine exists_orderOf_eq_of_dvd_orderOf (x := y) ?_
    rw [← hy']
    exact orderOf_map_dvd (QuotientGroup.mk' H) y

/-- Cauchy's theorem, by strong induction on the order of the group. -/
