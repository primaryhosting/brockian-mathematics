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


theorem mid_surj (M : NMachine Sigma) (w : Vert M) : ∃ j, j < cV M ∧ mid M j = w := by
  refine ⟨(Fintype.equivFin (Vert M) w).val, (Fintype.equivFin (Vert M) w).isLt, ?_⟩
  unfold mid
  rw [dif_pos (show ((Fintype.equivFin (Vert M)) w).val < cV M from
    (Fintype.equivFin (Vert M) w).isLt)]
  simp

/-- The mode of the simulator. -/
inductive Mode (M : NMachine Sigma) where
  /-- `call u v i`: compute whether `v` is reachable from `u` within `2 ^ i` steps. -/
  | call (u v : Vert M) (i : ℕ)
  /-- `ret b`: return the value `b` to the caller. -/
  | ret (b : Bool)
  /-- `done b`: the computation has finished with answer `b`. -/
  | done (b : Bool)

/-- A stack frame `(u, v, i, j, ph)`. -/
abbrev Frame (M : NMachine Sigma) : Type := Vert M × Vert M × ℕ × ℕ × Bool

/-- A raw state of the simulator. -/
abbrev Raw (M : NMachine Sigma) : Type := Mode M × List (Frame M)

/-- Move on to the next candidate midpoint (or give up and return `false`). -/
