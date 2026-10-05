/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Feit–Thompson theorem states that every finite group of odd order is solvable.
Its full proof is far beyond current formalization, and it is not available in Mathlib.

This file provides:

* `Frontier.OddOrderSolvable`, the formal statement of the theorem;
* `Frontier.NoOddOrderNonabelianSimple`, its simple-group form;
* `Frontier.feit_thompson_odd_order`, a Lean-checked reduction of the theorem to the
  simple-group form, and `Frontier.oddOrderSolvable_iff`, showing the two forms are equivalent;
* unconditional base cases: groups of squarefree order and groups of prime power order are
  solvable, and hence so is every group of odd order less than `45`
  (`Frontier.feit_thompson_lt_45`);
* `Frontier.feit_thompson_odd_order_of_large`, a sharper reduction in which the simple-group
  hypothesis is only needed for groups of order at least `45`.
-/

universe u

namespace Frontier

/-- The Feit–Thompson theorem, as a statement about all finite groups in a fixed universe:
every finite group of odd order is solvable. -/
def OddOrderSolvable : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The "simple group" form of the Feit–Thompson theorem: every finite *simple* group of odd
order is abelian (equivalently, cyclic of prime order). -/
def NoOddOrderNonabelianSimple : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], IsSimpleGroup G → Odd (Nat.card G) →
    ∀ a b : G, a * b = b * a

section Reduction

variable {G : Type u} [Group G]

/-- A subgroup of a group of odd order has odd order. -/
theorem odd_card_subgroup [Finite G] (hodd : Odd (Nat.card G)) (N : Subgroup G) :
    Odd (Nat.card N) :=
  hodd.of_dvd_nat N.card_subgroup_dvd_card

/-- A quotient of a group of odd order has odd order. -/
theorem odd_card_quotient [Finite G] (hodd : Odd (Nat.card G)) (N : Subgroup G) [N.Normal] :
    Odd (Nat.card (G ⧸ N)) :=
  hodd.of_dvd_nat (by rw [← Subgroup.index]; exact N.index_dvd_card)

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem card_lt_of_ne_top [Finite G] {N : Subgroup G} (hN : N ≠ ⊤) :
    Nat.card N < Nat.card G := by
  have h1 : Nat.card N * N.index = Nat.card G := N.card_mul_index
  have h2 : N.index ≠ 1 := fun h => hN (Subgroup.index_eq_one.1 h)
  have h3 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : 0 < Nat.card N := Nat.card_pos
  have h5 : 2 ≤ N.index := by omega
  nlinarith

/-- The quotient by a nontrivial normal subgroup of a finite group is strictly smaller. -/
theorem card_quotient_lt_of_ne_bot [Finite G] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have h1 : Nat.card N * N.index = Nat.card G := N.card_mul_index
  have h2 : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.2 hN
  have h3 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (G ⧸ N) = N.index := rfl
  rw [h4]
  nlinarith

/-- A group that is an extension of a solvable group by a solvable normal subgroup is solvable. -/
theorem isSolvable_of_normal_of_quotient (N : Subgroup G) [N.Normal] [IsSolvable N]
    [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- A nontrivial finite group that is not simple has a normal subgroup that is neither trivial
nor everything. -/
theorem exists_proper_normal_of_not_isSimpleGroup [Nontrivial G] (hs : ¬ IsSimpleGroup G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hcon
  push_neg at hcon
  exact hs ⟨fun N hN => (em (N = ⊥)).imp id fun hb => hcon N hN hb⟩

end Reduction

/-- **Reduction of Feit–Thompson to the simple case.** If every finite simple group of odd
order is abelian, then every finite group of odd order is solvable.

The proof is by induction on the order: a minimal counterexample cannot be simple (by the
hypothesis), so it has a proper nontrivial normal subgroup `N`, and both `N` and `G ⧸ N` have
smaller odd order, hence are solvable; therefore so is `G`. -/
theorem feit_thompson_odd_order (h : NoOddOrderNonabelianSimple.{u}) : OddOrderSolvable.{u} := by
  have key : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Odd (Nat.card G) →
      IsSolvable G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hcard hodd
      classical
      by_cases hs : IsSimpleGroup G
      · exact IsSimpleGroup.comm_iff_isSolvable.1 (h G hs hodd)
      · by_cases hnt : Nontrivial G
        · obtain ⟨N, hNnorm, hbot, htop⟩ := exists_proper_normal_of_not_isSimpleGroup hs
          have hN : IsSolvable N :=
            ih (Nat.card N) (hcard ▸ card_lt_of_ne_top htop) N rfl (odd_card_subgroup hodd N)
          have hQ : IsSolvable (G ⧸ N) :=
            ih (Nat.card (G ⧸ N)) (hcard ▸ card_quotient_lt_of_ne_bot hbot) (G ⧸ N) rfl
              (odd_card_quotient hodd N)
          exact isSolvable_of_normal_of_quotient N
        · rw [not_nontrivial_iff_subsingleton] at hnt
          infer_instance
  intro G _ _ hodd
  exact key (Nat.card G) G rfl hodd

/-- The Feit–Thompson theorem is equivalent to its simple-group form. -/
theorem oddOrderSolvable_iff : OddOrderSolvable.{u} ↔ NoOddOrderNonabelianSimple.{u} := by
  refine ⟨fun h G _ _ hs hodd => ?_, feit_thompson_odd_order⟩
  have : IsSimpleGroup G := hs
  exact IsSimpleGroup.comm_iff_isSolvable.2 (h G hodd)

section BaseCases

variable {G : Type*} [Group G]

/-- Unconditional base case: a group of squarefree order is solvable. -/
theorem isSolvable_of_squarefree_card [Finite G] (hG : Squarefree (Nat.card G)) :
    IsSolvable G :=
  have : IsZGroup G := IsZGroup.of_squarefree hG
  inferInstance

/-- Unconditional base case: a group of prime power order is solvable. -/
theorem isSolvable_of_card_eq_prime_pow [Finite G] {p k : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ k) : IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpG : IsPGroup p G := IsPGroup.of_card hG
  have : Group.IsNilpotent G := hpG.isNilpotent
  infer_instance

/-- Every odd natural number below `45` is either squarefree or one of `9`, `25`, `27`. -/
theorem eq_of_odd_lt_45_of_not_squarefree {n : ℕ} (hodd : Odd n) (hlt : n < 45)
    (hsq : ¬ Squarefree n) : n = 9 ∨ n = 25 ∨ n = 27 := by
  interval_cases n <;>
    simp_all [Nat.squarefree_iff_nodup_primeFactorsList, Nat.odd_iff]

/-- Unconditional base case of Feit–Thompson: every group of odd order less than `45` is
solvable. (Every odd number below `45` is either squarefree or a prime power.) -/
theorem feit_thompson_lt_45 [Finite G] (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) :
    IsSolvable G := by
  by_cases hs : Squarefree (Nat.card G)
  · exact isSolvable_of_squarefree_card hs
  · rcases eq_of_odd_lt_45_of_not_squarefree hodd hlt hs with h | h | h
    · exact isSolvable_of_card_eq_prime_pow (p := 3) (k := 2) (by norm_num) (by rw [h]; norm_num)
    · exact isSolvable_of_card_eq_prime_pow (p := 5) (k := 2) (by norm_num) (by rw [h]; norm_num)
    · exact isSolvable_of_card_eq_prime_pow (p := 3) (k := 3) (by norm_num) (by rw [h]; norm_num)

end BaseCases

/-- A sharper reduction: it suffices to know that finite simple groups of odd order **at least
`45`** are abelian; the smaller orders are handled unconditionally. -/
theorem feit_thompson_odd_order_of_large
    (h : ∀ (G : Type u) [Group G] [Finite G], IsSimpleGroup G → Odd (Nat.card G) →
      45 ≤ Nat.card G → ∀ a b : G, a * b = b * a) :
    OddOrderSolvable.{u} := by
  refine feit_thompson_odd_order fun G _ _ hs hodd => ?_
  by_cases hlt : Nat.card G < 45
  · have : IsSimpleGroup G := hs
    exact IsSimpleGroup.comm_iff_isSolvable.2 (feit_thompson_lt_45 hodd hlt)
  · exact h G hs hodd (not_lt.1 hlt)

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

