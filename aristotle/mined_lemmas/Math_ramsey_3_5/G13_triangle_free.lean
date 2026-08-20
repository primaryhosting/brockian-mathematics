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

lemma G13_triangle_free : ∀ A : Finset (Fin 13), ¬ G13.IsNClique 3 A := by
  intro A hA
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hA
  exact adj13_no_triangle a b c hab hbc hac

/-- Any five vertices of `Fin 13`, listed in increasing order, contain an edge of `G13`. -/
