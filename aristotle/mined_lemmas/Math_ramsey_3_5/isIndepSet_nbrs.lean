import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Cliques and independent sets inside a finite set of vertices -/

section General

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : Finset V} {n : ℕ} {v : V}

/-- `CliqueOn G s n` : the vertex set `s` contains a clique of `G` with `n` vertices. -/

lemma isIndepSet_nbrs {v : V} (hv : v ∈ s) (h3 : ¬ CliqueOn G s 3) :
    G.IsIndepSet ((nbrs G s v : Finset V) : Set V) := by
  intro x hx y hy hxy hadj
  simp only [Finset.coe_filter, Set.mem_setOf_eq, nbrs] at hx hy
  refine h3 (cliqueOn_of_clique (A := {v, x, y}) ?_ ?_ ?_)
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hx.1
    · exact hy.1
  · have hvx : v ≠ x := fun h => G.irrefl (h ▸ hx.2)
    have hvy : v ≠ y := fun h => G.irrefl (h ▸ hy.2)
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact hx.2
        | exact hy.2
        | exact hadj
        | exact hx.2.symm
        | exact hy.2.symm
        | exact hadj.symm
  · have hvx : v ≠ x := fun h => G.irrefl (h ▸ hx.2)
    have hvy : v ≠ y := fun h => G.irrefl (h ▸ hy.2)
    rw [Finset.card_insert_of_notMem (by simp [hvx, hvy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]

/-- Adding `v` to an independent set of non-neighbours of `v` keeps it independent. -/
