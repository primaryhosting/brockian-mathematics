import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


universe u'

namespace Frontier

/-- The Feit–Thompson odd order theorem, as a proposition: every finite group of odd order
is solvable. -/

private theorem solvable_of_odd_aux
    (hsimple : ∀ (S : Type u') [Group S] [Finite S],
      IsSimpleGroup S → Odd (Nat.card S) → IsSolvable S) :
    ∀ (n : ℕ) (G : Type u') [Group G] [Finite G],
      Nat.card G ≤ n → Odd (Nat.card G) → IsSolvable G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hle _
    exact absurd hle (by simpa using Nat.card_pos.ne')
  | succ n ih =>
    intro G _ _ hle hodd
    rcases subsingleton_or_nontrivial G with _ | _
    · infer_instance
    by_cases hsim : IsSimpleGroup G
    · exact hsimple G hsim hodd
    obtain ⟨N, hNnorm, hNbot, hNtop⟩ :=
      exists_proper_nontrivial_normal_of_not_isSimpleGroup G hsim
    have _ : N.Normal := hNnorm
    have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hNpos : 0 < Nat.card N := Nat.card_pos
    have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have hNone : 1 < Nat.card N := by
      have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hNbot
      exact Finite.one_lt_card_iff_nontrivial.2 this
    have hQone : 1 < Nat.card (G ⧸ N) := by
      rcases Nat.lt_or_ge 1 (Nat.card (G ⧸ N)) with h | h
      · exact h
      · exact absurd (Subgroup.index_eq_one.1 (le_antisymm h hQpos)) hNtop
    have hNlt : Nat.card N < Nat.card G := by
      rw [hcard]; nlinarith
    have hQlt : Nat.card (G ⧸ N) < Nat.card G := by
      rw [hcard]; nlinarith
    have hNodd : Odd (Nat.card N) := odd_of_dvd_odd (Subgroup.card_subgroup_dvd_card N) hodd
    have hQodd : Odd (Nat.card (G ⧸ N)) :=
      odd_of_dvd_odd (Subgroup.card_quotient_dvd_card N) hodd
    have _ : IsSolvable N := ih N (by omega) hNodd
    have _ : IsSolvable (G ⧸ N) := ih (G ⧸ N) (by omega) hQodd
    refine solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/--
**Feit–Thompson, reduced to the simple case.**

Assuming that every finite *simple* group of odd order is solvable (i.e. that there is no
simple counterexample), every finite group of odd order is solvable.

The full Feit–Thompson theorem is the statement that the hypothesis `hsimple` holds; this
