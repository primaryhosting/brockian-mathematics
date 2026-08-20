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


theorem DMachine.toNMachine_accepts (D : DMachine Sigma) (x : List Sigma) :
    D.toNMachine.Accepts x ↔ D.Accepts x := by
  constructor
  · rintro ⟨s, hs, hacc⟩
    have key : ∀ a b : D.S, Relation.ReflTransGen (D.toNMachine.edge x) a b →
        ∃ k, (D.move x)^[k] a = b := by
      intro a b h
      induction h with
      | refl => exact ⟨0, rfl⟩
      | tail _ hstep ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply', hk]
        exact hstep.symm
    obtain ⟨k, hk⟩ := key _ _ hs
    refine ⟨k, ?_⟩
    have hk' : (D.move x)^[k] D.start = s := hk
    rw [hk']
    exact hacc
  · rintro ⟨k, hk⟩
    refine ⟨(D.move x)^[k] D.start, ?_, hk⟩
    clear hk
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail rfl

