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


theorem reachIn_iff_reflTransGen [Fintype V] {i : ℕ} (hi : Fintype.card V ≤ 2 ^ i)
    (u v : V) : reachIn E i u v ↔ Relation.ReflTransGen E u v := by
  refine ⟨reachIn_imp_reflTransGen, fun h => ?_⟩
  obtain ⟨l, hl, hp⟩ := pathOf_short_of_reflTransGen h
  exact reachIn_of_pathOf i l u v hp (le_trans hl hi)

end CS

import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach

/-!
# The state space of the Savitch simulator

Given a nondeterministic machine `M`, Savitch's algorithm explores the configuration
graph of `M` by the recursion

`reach (i+1) u v  ↔  ∃ w, reach i u w ∧ reach i w v`.

Implemented iteratively, its memory consists of a *mode* (a pending call, a returned
Boolean, or the final answer) together with a *stack* of at most `K` frames, each frame
recording `(u, v, i, j, ph)`: the endpoints of the pending call, its level, the index
`j` of the midpoint currently being tried, and a phase bit telling which of the two
halves is being computed.

This file sets up these raw states, the well-formedness predicate bounding the stack,
and the resulting cardinality bound (the states are encoded into a fixed finite type).
-/

namespace CS
namespace Savitch

variable {Sigma : Type}

/-- A `Bool`-valued classical decision procedure. -/
