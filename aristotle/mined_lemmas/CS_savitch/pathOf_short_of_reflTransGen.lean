import Mathlib

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
import RequestProject.Savitch.Enc

/-!
# The Savitch simulator and its correctness

We build, from a nondeterministic machine `M` and a recursion depth `K`, a
deterministic machine `savitchDM M K` which decides, by Savitch's recursive midpoint
search, whether the sink vertex `none` of the configuration graph of `M` is reachable
from the start vertex within `2 ^ K` steps.  If `cV M ≤ 2 ^ K` this is exactly
acceptance by `M`.
-/

namespace CS
namespace Savitch

variable {Sigma : Type}


theorem pathOf_short_of_reflTransGen [Fintype V] {u v : V}
    (h : Relation.ReflTransGen E u v) :
    ∃ l ≤ Fintype.card V, PathOf E l u v := by
  classical
  have hex : ∃ l, PathOf E l u v := pathOf_of_reflTransGen h
  set l := Nat.find hex with hlk
  have hl : PathOf E l u v := Nat.find_spec hex
  have hmin : ∀ l' < l, ¬ PathOf E l' u v := fun l' hl' => Nat.find_min hex hl'
  refine ⟨l, ?_, hl⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨p, hp0, hpl, hstep⟩ := hl
  have hnotinj : ¬ Function.Injective (fun j : Fin (l + 1) => p j) := by
    intro hinj
    have := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at this
    omega
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨a, b, hab, hne'⟩ := hnotinj
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · obtain ⟨l', hl', hp'⟩ :=
      exists_shorter_pathOf hp0 hpl hstep (a := (a : ℕ)) (b := (b : ℕ))
        (by exact_mod_cast hlt) (by omega) hab
    exact hmin l' hl' hp'
  · obtain ⟨l', hl', hp'⟩ :=
      exists_shorter_pathOf hp0 hpl hstep (a := (b : ℕ)) (b := (a : ℕ))
        (by exact_mod_cast hlt) (by omega) hab.symm
    exact hmin l' hl' hp'

/-- On a finite vertex set, `reachIn E i` is exactly reachability, provided
`card V ≤ 2 ^ i`. -/
