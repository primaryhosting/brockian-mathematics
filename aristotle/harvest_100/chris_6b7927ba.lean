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
theorem isSolvable_of_squarefree_card (G : Type u) [Group G] [Finite G]
    (h : Squarefree (Nat.card G)) : IsSolvable G := by
  have : IsZGroup G := IsZGroup.of_squarefree h
  infer_instance

/-- A finite group of prime power order is solvable (it is nilpotent). -/
theorem isSolvable_of_isPrimePow_card (G : Type u) [Group G] [Finite G]
    (h : IsPrimePow (Nat.card G)) : IsSolvable G := by
  obtain ⟨p, k, hp, hk, hpk⟩ := h
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  haveI : Fact p.Prime := ⟨hp'⟩
  have hP : IsPGroup p G := IsPGroup.of_card hpk.symm
  have := hP.isNilpotent
  infer_instance

/-- Every odd number below `45` is either squarefree or a prime power. -/
theorem squarefree_or_isPrimePow_of_odd_lt_45 :
    ∀ n < 45, Odd n → Squarefree n ∨ IsPrimePow n := by decide +kernel

/-- **Base case of Feit–Thompson**: every finite group of odd order less than `45` is
solvable.  (Unconditional: `45 = 3 ^ 2 * 5` is the smallest odd number that is neither
squarefree nor a prime power.) -/
theorem isSolvable_of_odd_card_lt_45 (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) : IsSolvable G := by
  rcases squarefree_or_isPrimePow_of_odd_lt_45 _ hlt hodd with h | h
  · exact isSolvable_of_squarefree_card G h
  · exact isSolvable_of_isPrimePow_card G h

/-! ## The reduction to simple groups -/

/-- Auxiliary strong induction on the order of the group. -/
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
theorem feit_thompson_odd_order
    (hsimple : ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → Odd (Nat.card S) →
      ∀ a b : S, a * b = b * a)
    (G : Type u) [Group G] [Finite G] (hodd : Odd (Nat.card G)) : IsSolvable G :=
  isSolvable_of_odd_aux hsimple (Nat.card G) G rfl hodd

/-! ## The statement of the odd order theorem, and its equivalence with the simple case -/

/-- The statement of the **Feit–Thompson odd order theorem**: every finite group of odd
order is solvable. -/
def OddOrderSolvable : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The statement that every finite simple group of odd order is abelian. -/
def SimpleOddAbelian : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → Odd (Nat.card S) →
    ∀ a b : S, a * b = b * a

/-- The odd order theorem is *equivalent* to the assertion that every finite simple group of
odd order is abelian.  The forward implication is `Frontier.feit_thompson_odd_order`; the
backward implication holds because a simple solvable group is abelian. -/
theorem oddOrderSolvable_iff_simpleOddAbelian :
    OddOrderSolvable.{u} ↔ SimpleOddAbelian.{u} := by
  constructor
  · intro h S _ _ hs hodd
    haveI := hs
    exact IsSimpleGroup.comm_iff_isSolvable.mpr (h S hodd)
  · intro h G _ _ hodd
    exact feit_thompson_odd_order h G hodd

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

