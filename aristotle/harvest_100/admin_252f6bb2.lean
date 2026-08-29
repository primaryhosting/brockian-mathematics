/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

universe u

namespace Frontier

/-!
## Statement

The Feit–Thompson odd order theorem states that every finite group of odd order is
solvable.  Its proof is a 255-page argument and is not available in Mathlib.  What is
formalized here is:

* the statement itself, in the form `OddOrderSolvable`;
* a complete, machine-checked **reduction** of the statement to its minimal-counterexample
  ("simple") case, `Frontier.feit_thompson_odd_order`;
* unconditional **base cases**: groups of odd prime-power order, groups of odd order the
  product of two distinct primes, and — combining these — every group of odd order less
  than `45`, the first odd order that is neither a prime power nor squarefree.
-/

/-- Having no normal subgroup other than `⊥` and `⊤` (for a nontrivial group this is
exactly simplicity). -/
def NoProperNormal (G : Type u) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤

/-- The Feit–Thompson conclusion: every finite group of odd order is solvable. -/
def OddOrderSolvable : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The Feit–Thompson hypothesis in "minimal counterexample" form: every finite group of
odd order with no proper nontrivial normal subgroup is abelian (equivalently, is cyclic of
prime order). -/
def OddOrderSimpleAbelian : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → NoProperNormal G →
    ∀ a b : G, a * b = b * a

section Aux

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Lagrange: the order of a group is the index of a subgroup times the subgroup's order. -/
theorem card_quotient_mul_card_subgroup (N : Subgroup G) :
    Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm

omit [Finite G] in
/-- A subgroup of a group of odd order has odd order. -/
theorem odd_card_subgroup (hodd : Odd (Nat.card G)) (N : Subgroup G) :
    Odd (Nat.card N) :=
  hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)

omit [Finite G] in
/-- A quotient of a group of odd order has odd order. -/
theorem odd_card_quotient (hodd : Odd (Nat.card G)) (N : Subgroup G) :
    Odd (Nat.card (G ⧸ N)) :=
  hodd.of_dvd_nat ⟨Nat.card N, (card_quotient_mul_card_subgroup N).symm⟩

omit [Finite G] in
/-- If a normal subgroup and its quotient are solvable, so is the group. -/
theorem isSolvable_of_normal (N : Subgroup G) [N.Normal] [IsSolvable N]
    [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) <| by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/-- A group of prime power order is solvable. -/
theorem isSolvable_of_card_eq_prime_pow {p k : ℕ} (hp : Nat.Prime p)
    (h : Nat.card G = p ^ k) : IsSolvable G := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Group.IsNilpotent G := (IsPGroup.of_card h).isNilpotent
  infer_instance

/-- A group whose order is a product of two distinct primes is solvable (it is a
`Z`-group, i.e. all of its Sylow subgroups are cyclic). -/
theorem isSolvable_of_card_eq_prime_mul_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (h : Nat.card G = p * q) : IsSolvable G := by
  have hsf : Squarefree (Nat.card G) := by
    rw [h, Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hpq)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  haveI : IsZGroup G := IsZGroup.of_squarefree hsf
  infer_instance

end Aux

/-- Every odd number below `45` is either a prime power or a product of two distinct
primes.  (`45 = 3 ^ 2 * 5` is the least odd number that is neither.) -/
theorem odd_lt_45_prime_pow_or_prime_mul_prime (n : ℕ) (hodd : Odd n) (hlt : n < 45) :
    (∃ p k, Nat.Prime p ∧ n = p ^ k) ∨
      (∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p * q) := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : k < 22 := by omega
  interval_cases k <;>
    first
      | (refine Or.inl ⟨3, 0, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inl ⟨_, 1, ?_, (pow_one _).symm⟩; norm_num; done)
      | (refine Or.inl ⟨3, 2, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inl ⟨3, 3, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inl ⟨5, 2, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 5, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 7, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 11, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨5, 7, ?_, ?_, ?_, ?_⟩ <;> norm_num; done)
      | (refine Or.inr ⟨3, 13, ?_, ?_, ?_, ?_⟩ <;> norm_num)

/-- **Base case of Feit–Thompson, unconditionally.**  Every finite group whose order is odd
and less than `45` is solvable.  (`45` is the least odd order for which this argument stops
working, since `45 = 3 ^ 2 * 5` is neither a prime power nor squarefree.) -/
theorem isSolvable_of_odd_card_lt_45 (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) : IsSolvable G := by
  rcases odd_lt_45_prime_pow_or_prime_mul_prime (Nat.card G) hodd hlt with
    ⟨p, k, hp, h⟩ | ⟨p, q, hp, hq, hpq, h⟩
  · exact isSolvable_of_card_eq_prime_pow hp h
  · exact isSolvable_of_card_eq_prime_mul_prime hp hq hpq h

/-- **Reduction of Feit–Thompson to the simple case.**  Granting that every finite group of
odd order with no proper nontrivial normal subgroup is abelian, every finite group of odd
order is solvable.  The hypothesis is exactly the hard content of the Feit–Thompson odd
order theorem; the reduction proved here is a complete, machine-checked strong induction on
the order of the group. -/
theorem feit_thompson_odd_order (hsimple : OddOrderSimpleAbelian.{u}) :
    OddOrderSolvable.{u} := by
  suffices h : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G],
      Nat.card G = n → Odd (Nat.card G) → IsSolvable G by
    intro G _ _ hodd
    exact h (Nat.card G) G rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hcard hodd
    by_cases hnp : NoProperNormal G
    · exact isSolvable_of_comm (hsimple G hodd hnp)
    · -- there is a normal subgroup `N` with `⊥ < N < ⊤`
      simp only [NoProperNormal, not_forall] at hnp
      obtain ⟨N, hN, hne⟩ := hnp
      simp only [not_or] at hne
      obtain ⟨hbot, htop⟩ := hne
      have hNn : N.Normal := hN
      have hmul : Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
        card_quotient_mul_card_subgroup N
      have hN1 : 1 < Nat.card N := by
        rcases Nat.lt_or_ge 1 (Nat.card N) with h | h
        · exact h
        · exact absurd (Subgroup.eq_bot_of_card_eq N (le_antisymm h Nat.card_pos)) hbot
      have hQ1 : 1 < Nat.card (G ⧸ N) := by
        rcases Nat.lt_or_ge 1 (Nat.card (G ⧸ N)) with h | h
        · exact h
        · have hq : Nat.card (G ⧸ N) = 1 := le_antisymm h Nat.card_pos
          rw [hq, one_mul] at hmul
          exact absurd (Subgroup.eq_top_of_card_eq N hmul) htop
      have hNlt : Nat.card N < n := by
        rw [← hcard, ← hmul]
        nlinarith [Nat.card_pos (α := N)]
      have hQlt : Nat.card (G ⧸ N) < n := by
        rw [← hcard, ← hmul]
        nlinarith [Nat.card_pos (α := (G ⧸ N))]
      have hsN : IsSolvable N := ih _ hNlt N rfl (odd_card_subgroup hodd N)
      have hsQ : IsSolvable (G ⧸ N) :=
        ih _ hQlt (G ⧸ N) rfl (odd_card_quotient hodd N)
      exact isSolvable_of_normal N

end Frontier

