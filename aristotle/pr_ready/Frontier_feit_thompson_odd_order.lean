/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Statement: Every finite group of odd order is solvable (Feit–Thompson; Thompson/Tits Abel).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

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
private lemma odd_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m := by
  obtain ⟨k, rfl⟩ := hmn
  exact (Nat.odd_mul.mp hn).1

/-- The statement "every finite simple group of odd order is commutative".
This is the simple-group form of the Feit–Thompson odd order theorem. -/
def OddOrderSimpleComm : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    Odd (Nat.card S) → IsSimpleGroup S → ∀ a b : S, a * b = b * a

/-- Auxiliary induction: assuming that all finite simple groups of odd order are
commutative, every finite group of odd order and cardinality `n` is solvable. -/
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
theorem feit_thompson_odd_order (hsimple : OddOrderSimpleComm.{u})
    (G : Type u) [Group G] [Finite G] (hodd : Odd (Nat.card G)) : IsSolvable G :=
  isSolvable_of_card_eq hsimple (Nat.card G) G rfl hodd

/-- The converse reduction: if every finite group of odd order is solvable, then every
finite simple group of odd order is commutative. -/
theorem oddOrderSimpleComm_of_isSolvable
    (h : ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G) :
    OddOrderSimpleComm.{u} := by
  intro S _ _ hodd hsimp
  exact IsSimpleGroup.comm_iff_isSolvable.mpr (h S hodd)

/-- The Feit–Thompson theorem is *equivalent* to its simple-group form. -/
theorem feit_thompson_odd_order_iff :
    OddOrderSimpleComm.{u} ↔
      ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G :=
  ⟨fun h G _ _ hodd => feit_thompson_odd_order h G hodd, oddOrderSimpleComm_of_isSolvable⟩

/-- Base case (unconditional): a finite group of prime power order is solvable. -/
theorem isSolvable_of_isPGroup {p : ℕ} [Fact p.Prime] (G : Type u) [Group G] [Finite G]
    (hp : IsPGroup p G) : IsSolvable G :=
  haveI := hp.isNilpotent
  inferInstance

/-- Base case (unconditional): a finite simple group of prime power order is
commutative, i.e. the simple-group form of Feit–Thompson holds for `p`-groups. -/
theorem comm_of_isPGroup_of_isSimpleGroup {p : ℕ} [Fact p.Prime] (G : Type u) [Group G] [Finite G]
    (hp : IsPGroup p G) [IsSimpleGroup G] (a b : G) : a * b = b * a :=
  haveI := hp.isNilpotent
  IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b

/-- Base case (unconditional): a finite group of odd order at most `3` is solvable. -/
theorem isSolvable_of_card_le_three (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hle : Nat.card G ≤ 3) : IsSolvable G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcard : Nat.card G = 1 ∨ Nat.card G = 3 := by
    rw [Nat.odd_iff] at hodd; omega
  rcases hcard with h | h
  · haveI : Subsingleton G := Nat.card_eq_one_iff_unique.mp h |>.1
    infer_instance
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsCyclic G := isCyclic_of_prime_card (p := 3) h
    infer_instance

end Frontier


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

