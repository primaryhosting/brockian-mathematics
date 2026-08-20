import Mathlib
import RequestProject.Ramsey

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

import Mathlib

/-!
# The Ramsey number `R(3,5) = 14`

This file proves that `14` is the least `n` such that every simple graph on `n` vertices
contains a triangle (a `3`-clique) or an independent set of size `5` (a `5`-clique of the
complement).
-/

namespace Math

open Finset SimpleGraph

section Bounds

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `NoCliqueIn G n s` says that `G` has no `n`-clique contained in the vertex set `s`. -/

theorem exists_triangle_or_indep_five {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : 14 ≤ Fintype.card V) (G : SimpleGraph V) :
    (∃ s : Finset V, G.IsNClique 3 s) ∨ (∃ t : Finset V, Gᶜ.IsNClique 5 t) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hb := bound_five (G := G) (s := Finset.univ)
    (fun t _ ht => h1 t ht) (fun t _ ht => h2 t ht)
  rw [Finset.card_univ] at hb
  omega

/-- The graph on `Fin n`, `n ≤ 13`, obtained by restricting `graph13`. -/
