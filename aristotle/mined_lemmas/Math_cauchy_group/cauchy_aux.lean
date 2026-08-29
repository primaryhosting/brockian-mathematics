/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open MulAction Subgroup

/-- From an element whose order is divisible by `p` we get an element of order exactly `p`. -/

theorem cauchy_aux {p : ℕ} (hp : p.Prime) :
    ∀ (n : ℕ) (G : Type*) [Group G] [Finite G], Nat.card G = n → p ∣ n →
      ∃ g : G, orderOf g = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hcard hdvd
    subst hcard
    by_cases hex : ∃ H : Subgroup G, H ≠ ⊤ ∧ p ∣ Nat.card H
    · obtain ⟨H, hne, hdvdH⟩ := hex
      have hlt : Nat.card H < Nat.card G := by
        have := Subgroup.card_mul_index H
        have h1 : 1 < H.index := Subgroup.one_lt_index_of_ne_top hne
        have h2 : 0 < Nat.card H := Nat.card_pos
        nlinarith [this]
      obtain ⟨g, hg⟩ := ih (Nat.card H) hlt H rfl hdvdH
      exact ⟨(g : G), (orderOf_coe g).trans hg⟩
    · push_neg at hex
      have hproper : ∀ H : Subgroup G, H ≠ ⊤ → ¬ p ∣ Nat.card H := fun H hH => hex H hH
      have hcent : p ∣ Nat.card (Subgroup.center G) := prime_dvd_card_center hp hdvd hproper
      have htop : Subgroup.center G = ⊤ := by
        by_contra hne
        exact hproper _ hne hcent
      have hcomm : ∀ a b : G, a * b = b * a := by
        intro a b
        have : a ∈ Subgroup.center G := by rw [htop]; trivial
        exact (Subgroup.mem_center_iff.mp this b).symm
      have hnontriv : Nontrivial G := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        have hple : p ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd
        have := hp.two_le
        omega
      obtain ⟨x, hx⟩ := exists_ne (1 : G)
      by_cases hxp : p ∣ orderOf x
      · exact exists_orderOf_eq_of_dvd_orderOf x hxp
      · set H : Subgroup G := Subgroup.zpowers x with hH
        haveI : H.Normal := ⟨fun a ha g => by
          have : g * a * g⁻¹ = a := by rw [hcomm g a, mul_assoc, mul_inv_cancel, mul_one]
          rwa [this]⟩
        have hcardH : Nat.card H = orderOf x := Nat.card_zpowers x
        have hcardH1 : 1 < Nat.card H := by
          rw [hcardH]
          have h1 : 0 < orderOf x := orderOf_pos x
          have h2 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
          omega
        have hmul := Subgroup.card_mul_index H
        have hindexdvd : p ∣ H.index := by
          have : p ∣ Nat.card H * H.index := hmul ▸ hdvd
          rcases (Nat.Prime.dvd_mul hp).mp this with h | h
          · exact absurd (hcardH ▸ h) hxp
          · exact h
        have hindexlt : H.index < Nat.card G := by
          have h2 : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
          nlinarith [hmul]
        have hquot : Nat.card (G ⧸ H) = H.index := rfl
        obtain ⟨q, hq⟩ := ih H.index hindexlt (G ⧸ H) hquot hindexdvd
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        have hdvdg : p ∣ orderOf g := by
          have := orderOf_map_dvd (QuotientGroup.mk' H) g
          rw [show (QuotientGroup.mk' H) g = (QuotientGroup.mk g : G ⧸ H) from rfl, hq] at this
          exact this
        exact exists_orderOf_eq_of_dvd_orderOf g hdvdg

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order `p`. -/
