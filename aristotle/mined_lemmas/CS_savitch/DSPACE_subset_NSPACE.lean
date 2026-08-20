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


theorem DSPACE_subset_NSPACE (f : ℕ → ℕ) : DSPACE Sigma f ⊆ NSPACE Sigma f := by
  rintro L ⟨c, hc⟩
  refine ⟨c, fun n => ?_⟩
  obtain ⟨D, hcard, hD⟩ := hc n
  exact ⟨D.toNMachine, hcard, fun x hx => (D.toNMachine_accepts x).trans (hD x hx)⟩

end CS

import Mathlib

/-!
# Bounded reachability and the Savitch doubling relation

`CS.reachIn E i u v` says that `v` can be reached from `u` by a path of length at most
`2 ^ i`.  It satisfies the Savitch recursion `reachIn E (i+1) u v ↔ ∃ w, reachIn E i u w
∧ reachIn E i w v` *by definition*, and on a finite vertex set `V` it coincides with
reachability as soon as `card V ≤ 2 ^ i`.
-/

namespace CS

variable {V : Type} {E : V → V → Prop}

/-- `PathOf E l u v`: there is a walk of length exactly `l` from `u` to `v`. -/
