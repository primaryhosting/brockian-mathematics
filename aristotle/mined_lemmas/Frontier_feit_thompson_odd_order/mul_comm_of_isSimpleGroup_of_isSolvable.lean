import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The statement of the Feit–Thompson (odd order) theorem: every finite group of odd
order is solvable. -/

theorem mul_comm_of_isSimpleGroup_of_isSolvable {G : Type} [Group G] [IsSimpleGroup G]
    [h : IsSolvable G] (a b : G) : a * b = b * a := by
  obtain ⟨n, hn⟩ := h.solvable
  have hc : commutator G = ⊥ := by
    cases n with
    | zero =>
      have h1 : derivedSeries G 1 ≤ derivedSeries G 0 := derivedSeries_antitone G (Nat.zero_le 1)
      rw [hn, derivedSeries_one] at h1
      exact le_bot_iff.mp h1
    | succ m => rw [← IsSimpleGroup.derivedSeries_succ (n := m)]; exact hn
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hmem : ⁅a, b⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hc] at hmem
  simpa using hmem

/-- The Feit–Thompson theorem is *equivalent* to its simple-group case: every finite group of
odd order is solvable if and only if every finite simple group of odd order is abelian. -/
