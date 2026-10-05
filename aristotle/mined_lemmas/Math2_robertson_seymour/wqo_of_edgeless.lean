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

theorem wqo_of_edgeless (f : ℕ → FinGraph) (hf : ∀ i, Edgeless (f i)) :
    ∃ i j, i < j ∧ IsMinor (f i) (f j) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ∀ i, (f i₀).n ≤ (f i).n := by
    have hne : {k | ∃ i, (f i).n = k}.Nonempty := ⟨(f 0).n, 0, rfl⟩
    obtain ⟨i₀, hi₀⟩ := Nat.sInf_mem hne
    refine ⟨i₀, fun i => ?_⟩
    rw [hi₀]
    exact Nat.sInf_le ⟨i, rfl⟩
  refine ⟨i₀, i₀ + 1, Nat.lt_succ_self _,
    isMinor_of_subgraphEmbed ⟨⟨Fin.castLE (hi₀ (i₀ + 1)), Fin.castLE_injective _⟩, ?_⟩⟩
  intro u v huv
  exact absurd huv (hf i₀ u v)

end Math2

