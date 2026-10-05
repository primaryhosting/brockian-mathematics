import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- A finite simple graph, presented as a simple graph on the vertex set `Fin n`. -/
structure FinGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency structure. -/
  adj : SimpleGraph (Fin n)

namespace FinGraph

/-- The graph obtained from `H` by contracting the edge `{a, b}`: the vertex `b` is deleted and
its neighbourhood is added to that of `a`. -/

theorem exists_finite_generating (hA : WellQuasiOrderedByMinors) (D : Set FinGraph) :
    ∃ S : Set FinGraph, S.Finite ∧ S ⊆ D ∧ ∀ K ∈ D, ∃ H ∈ S, IsMinor H K := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ l : List D, ∃ K : D, ∀ H ∈ l, ¬ IsMinor (H : FinGraph) (K : FinGraph) := by
    intro l
    obtain ⟨K, hKD, hK⟩ := hcon (Subtype.val '' {x : D | x ∈ l})
      ((List.finite_toSet l).image _) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    exact ⟨⟨K, hKD⟩, fun H hH => hK _ ⟨H, hH, rfl⟩⟩
  choose F hF using key
  let p : ℕ → List D := fun n => Nat.rec [] (fun _ l => l ++ [F l]) n
  have hps : ∀ n, p (n + 1) = p n ++ [F (p n)] := fun _ => rfl
  have hmem : ∀ n i, i < n → F (p i) ∈ p n := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      rw [hps]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact List.mem_append_left _ (ih i h)
      · exact List.mem_append_right _ (by simp)
  obtain ⟨i, j, hij, hminor⟩ := hA (fun n => (F (p n) : FinGraph))
  exact hF (p j) (F (p i)) (hmem j i hij) hminor

