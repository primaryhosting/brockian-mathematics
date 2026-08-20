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


theorem reachIn_mono {i j : ℕ} (hij : i ≤ j) {u v : V} (h : reachIn E i u v) :
    reachIn E j u v := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    exact this ▸ h
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact reachIn_succ_of j (ih (by omega))
    · have : i = j + 1 := le_antisymm hij h'
      exact this ▸ h

