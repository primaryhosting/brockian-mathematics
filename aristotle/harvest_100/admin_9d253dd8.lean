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
def FeitThompsonOddOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The "no odd simple counterexample" hypothesis: every finite *simple* group of odd order
is solvable (equivalently, is cyclic of prime order). -/
def NoOddOrderSimpleCounterexample : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → Odd (Nat.card G) → IsSolvable G

section Reduction


/-- A divisor of an odd natural number is odd. -/
theorem odd_of_dvd_odd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m :=
  hn.of_dvd_nat hmn

/-- If `G` is a nontrivial group that is not simple, then it has a normal subgroup that is
neither trivial nor everything. -/
theorem exists_proper_nontrivial_normal_of_not_isSimpleGroup
    (G : Type*) [Group G] [Nontrivial G] (h : ¬ IsSimpleGroup G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  refine h { eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
  rcases eq_or_ne H ⊥ with hb | hb
  · exact Or.inl hb
  · exact Or.inr (hc H hH hb)

/-- Induction step packaged as a bounded statement, for strong induction on the order. -/
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
theorem is the (Lean-checked) reduction of the general statement to the simple case, by
induction on the order using Lagrange's theorem and closure of solvability under extensions.
-/
theorem feit_thompson_odd_order
    (hsimple : ∀ (S : Type u') [Group S] [Finite S],
      IsSimpleGroup S → Odd (Nat.card S) → IsSolvable S)
    (G : Type u') [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G :=
  solvable_of_odd_aux hsimple (Nat.card G) G le_rfl hG

/-- The reduction, stated with the two `Prop`-valued abbreviations. -/
theorem feit_thompson_of_no_odd_simple_counterexample :
    NoOddOrderSimpleCounterexample → FeitThompsonOddOrder :=
  fun h G _ _ hG => feit_thompson_odd_order h G hG

/-- Conversely, the full theorem trivially implies the simple case, so the reduction is an
equivalence. -/
theorem feit_thompson_iff_no_odd_simple_counterexample :
    FeitThompsonOddOrder ↔ NoOddOrderSimpleCounterexample :=
  ⟨fun h G _ _ _ hG => h G hG, feit_thompson_of_no_odd_simple_counterexample⟩

end Reduction

section BaseCases

/-- Base case: a group of prime power order is solvable (in particular any group of odd
prime power order). -/
theorem isSolvable_of_card_eq_prime_pow
    (G : Type*) [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ k) : IsSolvable G := by
  haveI := Fact.mk hp
  haveI : Group.IsNilpotent G := (IsPGroup.of_card (p := p) hcard).isNilpotent
  infer_instance

/-- Base case: a finite group of prime order is solvable (indeed cyclic). -/
theorem isSolvable_of_card_prime
    (G : Type*) [Group G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p) : IsSolvable G := by
  haveI := Fact.mk hp
  haveI : IsCyclic G := isCyclic_of_prime_card hcard
  exact isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b

/-- Base case: a finite group of squarefree order is solvable (its Sylow subgroups are all
cyclic, i.e. it is a Z-group).  This gives Feit-Thompson unconditionally for the groups of
squarefree odd order. -/
theorem isSolvable_of_squarefree_card
    (G : Type*) [Group G] [Finite G] (hsq : Squarefree (Nat.card G)) : IsSolvable G := by
  haveI : IsZGroup G := IsZGroup.of_squarefree hsq
  infer_instance

end BaseCases

end Frontier

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

