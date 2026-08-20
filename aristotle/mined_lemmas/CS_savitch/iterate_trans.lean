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


theorem iterate_trans {k1 k2 : ℕ} {a b c : Raw M} (h1 : (rawNext M x)^[k1] a = b)
    (h2 : (rawNext M x)^[k2] b = c) : (rawNext M x)^[k1 + k2] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

/-- The inner loop of Savitch's algorithm: starting from the state that is about to
compute `reach i u (mid j)` with the frame `(u, v, i, j, false)` on the stack, the
simulator eventually returns whether some midpoint of index `≥ j` works. -/
