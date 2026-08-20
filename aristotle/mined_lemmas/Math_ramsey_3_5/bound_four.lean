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

theorem bound_four {s : Finset V} (h3 : NoCliqueIn G 3 s)
    (hk : NoCliqueIn Gᶜ 4 s) : s.card ≤ 8 := by
  by_contra hlt
  push_neg at hlt
  have hall : ∀ v ∈ s, (s ∩ G.neighborFinset v).card = 3 := by
    intro v hv
    have hd : (s ∩ G.neighborFinset v).card < 4 := nbr_card_lt hv h3 hk
    have hM : (s \ insert v (G.neighborFinset v)).card ≤ 5 :=
      bound_three (h3.mono Finset.sdiff_subset) (nonNbrs_noClique (k := 3) hv hk)
    have := card_split G s v
    omega
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hd : (s ∩ G.neighborFinset v).card = 3 := hall v hv
  have hM : (s \ insert v (G.neighborFinset v)).card ≤ 5 :=
    bound_three (h3.mono Finset.sdiff_subset) (nonNbrs_noClique (k := 3) hv hk)
  have hsplit := card_split G s v
  have heven : Even s.card := even_card_of_three_regular hall
  have : s.card = 9 := by omega
  rw [this] at heven
  simp [Nat.even_iff] at heven

/-- `R(3,5) ≤ 14`. -/
