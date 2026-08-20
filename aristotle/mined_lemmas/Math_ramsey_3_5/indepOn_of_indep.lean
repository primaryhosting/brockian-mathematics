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

lemma indepOn_of_indep {A : Finset V} (hA : A ⊆ s) (hind : G.IsIndepSet (A : Set V))
    (hn : n ≤ A.card) : IndepOn G s n := by
  obtain ⟨B, hB, hcard⟩ := Finset.exists_subset_card_eq hn
  exact ⟨B, hB.trans hA, hcard, hind.mono (by exact_mod_cast hB)⟩

/-- The neighbours of `v` inside `s`. -/
