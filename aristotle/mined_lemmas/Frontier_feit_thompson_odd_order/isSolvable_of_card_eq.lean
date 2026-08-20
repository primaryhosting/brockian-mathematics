/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)
import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Frontier

/-- Every divisor of an odd natural number is odd. -/

private theorem isSolvable_of_card_eq (hsimple : OddOrderSimpleComm.{u}) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Odd (Nat.card G) → IsSolvable G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hcard hodd
    rcases subsingleton_or_nontrivial G with _ | _
    · infer_instance
    by_cases hsimp : IsSimpleGroup G
    · exact IsSimpleGroup.comm_iff_isSolvable.mp (hsimple G hodd hsimp)
    · -- `G` is nontrivial and not simple, so it has a proper nontrivial normal subgroup `H`.
      obtain ⟨H, hHnorm, hbot, htop⟩ : ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ ∧ H ≠ ⊤ := by
        by_contra hcon
        push_neg at hcon
        refine hsimp ⟨fun H hH => ?_⟩
        by_cases hHb : H = ⊥
        · exact Or.inl hHb
        · exact Or.inr (hcon H hH hHb)
      haveI := hHnorm
      have hmul : H.index * Nat.card H = Nat.card G := H.index_mul_card
      haveI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hbot
      have hHcard : 1 < Nat.card H := Finite.one_lt_card
      have hHindex : 1 < H.index := Subgroup.one_lt_index_of_ne_top htop
      have hqcard : Nat.card (G ⧸ H) = H.index := (H.index_eq_card).symm
      -- both `H` and `G ⧸ H` are strictly smaller and of odd order
      haveI : IsSolvable H := by
        refine ih (Nat.card H) ?_ H rfl (odd_of_dvd ⟨H.index, by rw [← hmul, Nat.mul_comm]⟩ hodd)
        subst hcard
        nlinarith [hmul]
      haveI : IsSolvable (G ⧸ H) := by
        refine ih (Nat.card (G ⧸ H)) ?_ (G ⧸ H) rfl ?_
        · subst hcard
          rw [hqcard]
          nlinarith [hmul]
        · exact odd_of_dvd ⟨Nat.card H, by rw [hqcard, hmul]⟩ hodd
      exact solvable_of_ker_le_range H.subtype (QuotientGroup.mk' H)
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- **Feit–Thompson odd order theorem, Lean-checked reduction.**

Assuming the simple-group form of the theorem — every finite simple group of odd
order is commutative — every finite group of odd order is solvable.

The reduction is by strong induction on the order: a nontrivial non-simple group of
odd order has a proper nontrivial normal subgroup `H`, and both `H` and `G ⧸ H`
again have odd order and smaller cardinality, so the extension is solvable. -/
