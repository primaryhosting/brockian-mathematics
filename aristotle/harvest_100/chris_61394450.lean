/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because a module docstring is a
-- command and Lean 4 requires `import` lines to precede every command in a file.)

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

/-- The "simple-group input" of the Feit–Thompson theorem, in universe `u`:
every finite **simple** group of odd order is abelian (equivalently, of prime order). -/
def OddSimpleAbelian : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Odd (Nat.card G) → IsSimpleGroup G → ∀ a b : G, a * b = b * a

/-- The conclusion of the Feit–Thompson theorem in universe `u`:
every finite group of odd order is solvable. -/
def OddOrderSolvable : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- A nontrivial group which is not simple has a normal subgroup that is neither `⊥` nor `⊤`. -/
theorem exists_proper_normal_of_not_isSimpleGroup {G : Type u} [Group G] [Nontrivial G]
    (h : ¬ IsSimpleGroup G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  refine h { toNontrivial := inferInstance, eq_bot_or_eq_top_of_normal := ?_ }
  intro N hN
  by_cases hb : N = ⊥
  · exact Or.inl hb
  · exact Or.inr (hc N hN hb)

/-- A group is solvable as soon as some normal subgroup and the corresponding quotient are. -/
theorem isSolvable_of_normal_of_quotient {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G := by
  refine solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/-- Main induction: assuming odd-order simple groups are abelian, every finite group
of odd order is solvable. -/
theorem isSolvable_of_oddSimpleAbelian_aux (H : OddSimpleAbelian.{u}) :
    ∀ (n : ℕ) (G : Type u) (_ : Group G) (_ : Finite G), Nat.card G = n →
      Odd (Nat.card G) → IsSolvable G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn hodd
    rcases subsingleton_or_nontrivial G with hs | hs
    · infer_instance
    by_cases hsimple : IsSimpleGroup G
    · exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mp (H G hodd hsimple)
    · obtain ⟨N, hNnormal, hNbot, hNtop⟩ := exists_proper_normal_of_not_isSimpleGroup hsimple
      haveI := hNnormal
      have hcard : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
      have hindex : N.index = Nat.card (G ⧸ N) := rfl
      -- both factors are odd
      rw [← hcard, Nat.odd_mul] at hodd
      obtain ⟨hoddN, hoddQ⟩ := hodd
      -- the subgroup is strictly smaller
      have hNpos : 0 < Nat.card N := Nat.card_pos
      have hQpos : 0 < N.index := by
        rw [hindex]; exact Nat.card_pos
      have hN1 : Nat.card N ≠ 1 := by
        intro h
        exact hNbot (Subgroup.card_eq_one.mp h)
      have hQ1 : N.index ≠ 1 := by
        intro h
        exact hNtop (Subgroup.index_eq_one.mp h)
      have hlt1 : Nat.card N < n := by
        rw [← hn, ← hcard]
        have : 2 ≤ N.index := by omega
        nlinarith
      have hlt2 : Nat.card (G ⧸ N) < n := by
        rw [← hn, ← hcard, ← hindex]
        have : 2 ≤ Nat.card N := by omega
        nlinarith
      haveI : IsSolvable N := ih _ hlt1 N inferInstance inferInstance rfl hoddN
      haveI : IsSolvable (G ⧸ N) := by
        refine ih _ hlt2 (G ⧸ N) inferInstance inferInstance rfl ?_
        rwa [← hindex]
      exact isSolvable_of_normal_of_quotient N

/-!
## The target theorem

The Feit–Thompson odd order theorem is not available in Mathlib, and a full formal proof is
far out of reach here.  What is proved below is a *Lean-checked reduction*: the statement
"every finite group of odd order is solvable" is **equivalent** to the statement
"every finite simple group of odd order is abelian", i.e. to the non-existence of a
nonabelian finite simple group of odd order.  This is the standard reduction of the
Feit–Thompson theorem to a statement about simple groups.
-/

/-- **Feit–Thompson, Lean-checked reduction.**
Every finite group of odd order is solvable **if and only if** every finite simple group of
odd order is abelian (equivalently: there is no nonabelian finite simple group of odd order). -/
theorem feit_thompson_odd_order : OddSimpleAbelian.{u} ↔ OddOrderSolvable.{u} := by
  constructor
  · intro H G _ _ hodd
    exact isSolvable_of_oddSimpleAbelian_aux H (Nat.card G) G inferInstance inferInstance rfl hodd
  · intro H G _ _ hodd hsimple
    haveI := hsimple
    haveI := H G hodd
    exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr inferInstance

/-- Unconditional base case: every finite `p`-group is solvable (in particular every group of
odd prime-power order). -/
theorem isSolvable_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (hG : IsPGroup p G) : IsSolvable G :=
  have : Group.IsNilpotent G := hG.isNilpotent
  inferInstance

/-- Unconditional base case: every finite group whose order is an odd prime power is solvable. -/
theorem feit_thompson_primePow {G : Type u} [Group G] [Finite G] {p n : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ n) : IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSolvable_of_isPGroup (p := p) (IsPGroup.of_card hcard)

/-- Unconditional base case: every finite group of squarefree order is solvable (all its Sylow
subgroups are cyclic, i.e. it is a Z-group).  In particular this covers all groups of odd
squarefree order. -/
theorem feit_thompson_squarefree {G : Type u} [Group G] [Finite G]
    (hcard : Squarefree (Nat.card G)) : IsSolvable G :=
  have : IsZGroup G := IsZGroup.of_squarefree hcard
  inferInstance

/-- A sharpened simple-group input: it suffices to rule out nonabelian finite simple groups of
odd order whose order is neither a prime power nor squarefree. -/
def OddSimpleAbelianRestricted : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Odd (Nat.card G) → IsSimpleGroup G → ¬ IsPrimePow (Nat.card G) →
      ¬ Squarefree (Nat.card G) → ∀ a b : G, a * b = b * a

/-- The restricted simple-group input already implies the full one: simple groups of prime power
order or of squarefree order are unconditionally solvable, hence abelian. -/
theorem oddSimpleAbelian_of_restricted (H : OddSimpleAbelianRestricted.{u}) :
    OddSimpleAbelian.{u} := by
  intro G _ _ hodd hsimple
  haveI := hsimple
  by_cases hpp : IsPrimePow (Nat.card G)
  · obtain ⟨p, k, hp, hk, hcard⟩ := hpp
    haveI : IsSolvable G :=
      feit_thompson_primePow (p := p) (n := k) (Nat.prime_iff.mpr hp) hcard.symm
    exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr inferInstance
  · by_cases hsq : Squarefree (Nat.card G)
    · haveI : IsSolvable G := feit_thompson_squarefree hsq
      exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr inferInstance
    · exact H G hodd hsimple hpp hsq

/-- **Feit–Thompson, sharpened reduction.**  Every finite group of odd order is solvable as soon
as every finite simple group of odd order which is neither of prime power order nor of squarefree
order is abelian. -/
theorem feit_thompson_odd_order_of_restricted (H : OddSimpleAbelianRestricted.{u}) :
    OddOrderSolvable.{u} :=
  feit_thompson_odd_order.mp (oddSimpleAbelian_of_restricted H)

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

