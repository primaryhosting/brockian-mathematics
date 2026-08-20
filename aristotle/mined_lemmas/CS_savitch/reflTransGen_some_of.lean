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


theorem reflTransGen_some_of {a b : Vert M} (h : Relation.ReflTransGen (edgeX M x) a b) :
    ∀ s, a = some s → (b = none ∨ ∃ t, b = some t ∧ Relation.ReflTransGen (M.edge x) s t) := by
  induction h with
  | refl => intro s hs; exact Or.inr ⟨s, hs, Relation.ReflTransGen.refl⟩
  | @tail c b _ hcb ih =>
    intro s hs
    rcases ih s hs with hc | ⟨t, ht, hst⟩
    · subst hc
      exact absurd hcb (by cases b <;> exact id)
    · subst ht
      cases b with
      | none => exact Or.inl rfl
      | some w => exact Or.inr ⟨w, rfl, hst.tail hcb⟩

