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


theorem pathOf_of_reflTransGen {u v : V} (h : Relation.ReflTransGen E u v) :
    ∃ l, PathOf E l u v := by
  induction h with
  | refl => exact ⟨0, fun _ => u, rfl, rfl, by omega⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, p, hp0, hpl, hstep⟩ := ih
    refine ⟨l + 1, fun j => if j ≤ l then p j else c, by simp [hp0], by simp, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j l with h' | h'
    · have h1 : j ≤ l := by omega
      have h2 : j + 1 ≤ l := by omega
      simp only [h1, h2, if_pos]
      exact hstep j h'
    · have hj' : j = l := by omega
      subst hj'
      show E (if j ≤ j then p j else c) (if j + 1 ≤ j then p (j + 1) else c)
      rw [if_pos (le_refl j), if_neg (by omega : ¬ j + 1 ≤ j), hpl]
      exact hbc

/-- A walk with a repeated vertex can be shortened. -/
