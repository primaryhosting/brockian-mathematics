import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem mul_card_le_two_mul_card_edgeSet [DecidableRel G.Adj] (m : ℕ)
    (h : ∀ v : V, m ≤ G.degree v) :
    (m : ℤ) * (Fintype.card V : ℤ) ≤ 2 * (Nat.card G.edgeSet : ℤ) := by
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hlow : m * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc m * Fintype.card V = ∑ _v : V, m := by simp [mul_comm]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => h v)
  have hEcard : (G.edgeFinset.card : ℤ) = (Nat.card G.edgeSet : ℤ) := by
    rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  have hlow' : (m : ℤ) * (Fintype.card V : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) := by
    have : ((m * Fintype.card V : ℕ) : ℤ) ≤ ((2 * G.edgeFinset.card : ℕ) : ℤ) := by
      exact_mod_cast hsum ▸ hlow
    push_cast at this ⊢
    linarith
  rwa [hEcard] at hlow'

/-- Degrees and cardinalities of neighbour sets agree. -/
