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

theorem graph13_compl_cliqueFree_five : graph13ᶜ.CliqueFree 5 := by
  intro t ht
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, hba, hca, hcb, hda, hdb, hdc,
    hea, heb, hec, hed⟩ := exists_five_distinct ht.2
  have key : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → adj13 x y = false := by
    intro x hx y hy hxy
    have := ht.1 hx hy hxy
    simpa [graph13, Bool.not_eq_true] using this.2
  exact no_indep5_aux a b ⟨fun h => hba h.symm, key a ha b hb (fun h => hba h.symm)⟩
    c ⟨hca, hcb, key a ha c hc (fun h => hca h.symm), key b hb c hc (fun h => hcb h.symm)⟩
    d ⟨hda, hdb, hdc, key a ha d hd (fun h => hda h.symm), key b hb d hd (fun h => hdb h.symm),
      key c hc d hd (fun h => hdc h.symm)⟩
    e ⟨hea, heb, hec, hed, key a ha e he (fun h => hea h.symm), key b hb e he (fun h => heb h.symm),
      key c hc e he (fun h => hec h.symm), key d hd e he (fun h => hed h.symm)⟩

end Construction

/-- Every graph on at least `14` vertices contains a triangle or an independent set of size `5`. -/
