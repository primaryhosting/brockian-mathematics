import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

theorem exists_isPerfectMatching_of_involutive (sigma : V → V) (hadj : ∀ v, G.Adj v (sigma v))
    (hinv : ∀ v, sigma (sigma v) = v) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  refine ⟨{ verts := Set.univ
            Adj := fun v w => G.Adj v w ∧ sigma v = w
            adj_sub := fun h => h.1
            edge_vert := fun _ => Set.mem_univ _
            symm := ?_ }, ?_⟩
  · rintro v w ⟨h1, rfl⟩
    exact ⟨h1.symm, hinv v⟩
  · refine Subgraph.isPerfectMatching_iff.mpr fun v => ⟨sigma v, ⟨hadj v, rfl⟩, ?_⟩
    rintro y ⟨-, rfl⟩
    rfl

/-- Under Hall's condition, a bipartite graph carries an adjacency-respecting involution
(the matching partner map). -/
