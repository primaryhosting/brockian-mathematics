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
