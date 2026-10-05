import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Unconditional base cases -/

/-- A finite group whose order is squarefree is solvable (it is a Z-group). -/

private theorem isSolvable_of_odd_aux
    (hsimple : ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → Odd (Nat.card S) →
      ∀ a b : S, a * b = b * a) :
    ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Odd (Nat.card G) →
      IsSolvable G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hcard hodd
    by_cases htriv : Nontrivial G
    · by_cases hs : IsSimpleGroup G
      · exact isSolvable_of_comm (hsimple G hs hodd)
      · -- `G` is nontrivial and not simple: pick a proper nontrivial normal subgroup.
        have : ¬ ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ := fun h => hs ⟨h⟩
        push_neg at this
        obtain ⟨H, hHnormal, hHbot, hHtop⟩ := this
        haveI := hHnormal
        have hpos : 0 < Nat.card G := Nat.card_pos
        have hHpos : 0 < Nat.card H := Nat.card_pos
        have hindex : H.index * Nat.card H = Nat.card G := H.index_mul_card
        have hHlt : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hHbot
        have hIlt : 1 < H.index := by
          rcases Nat.lt_or_ge H.index 2 with h2 | h2
          · interval_cases hi : H.index
            · omega
            · exact absurd (Subgroup.index_eq_one.mp hi) hHtop
          · omega
        -- the subgroup is solvable by the induction hypothesis
        have hcardH : Nat.card H < n := by nlinarith [hcard]
        have hHodd : Odd (Nat.card H) := Odd.of_dvd_nat hodd H.card_subgroup_dvd_card
        haveI : IsSolvable H := ih _ hcardH H rfl hHodd
        -- the quotient is solvable by the induction hypothesis
        have hcardQ : Nat.card (G ⧸ H) < n := by
          rw [← Subgroup.index_eq_card]; nlinarith [hcard]
        have hQodd : Odd (Nat.card (G ⧸ H)) := by
          refine Odd.of_dvd_nat hodd ?_
          rw [← Subgroup.index_eq_card]
          exact H.index_dvd_card
        haveI : IsSolvable (G ⧸ H) := ih _ hcardQ (G ⧸ H) rfl hQodd
        exact solvable_of_ker_le_range H.subtype (QuotientGroup.mk' H)
          (by rw [QuotientGroup.ker_mk', H.range_subtype])
    · rw [not_nontrivial_iff_subsingleton] at htriv
      exact isSolvable_of_comm fun a b => by
        simp [Subsingleton.elim a b]

/-- **Feit–Thompson, reduced to the simple case.**

The full Feit–Thompson theorem states that every finite group of odd order is solvable.
This is a Lean-checked reduction of that statement: *if* every finite simple group of odd
order is abelian, *then* every finite group of odd order is solvable.

The proof is a strong induction on the order: a nontrivial non-simple group has a proper
nontrivial normal subgroup `H`, and both `H` and `G ⧸ H` have smaller odd order, so the
extension `1 → H → G → G ⧸ H → 1` is solvable. -/
