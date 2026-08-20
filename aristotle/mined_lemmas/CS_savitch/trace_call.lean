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


theorem trace_call : ∀ (i : ℕ) (u v : Vert M) (st : List (Frame M)),
    ∃ k, (rawNext M x)^[k] (Mode.call u v i, st)
      = (Mode.ret (toBool (reachIn (edgeX M x) i u v)), st) := by
  intro i
  induction i with
  | zero => intro u v st; exact ⟨1, by rw [Function.iterate_one, rawNext_call_zero]⟩
  | succ i ih =>
    intro u v st
    obtain ⟨k, hk⟩ := trace_loop M x i ih (cV M) 0 (by omega) (cV_pos M) u v st
    have heq : (∃ j', 0 ≤ j' ∧ j' < cV M ∧ reachIn (edgeX M x) i u (mid M j') ∧
        reachIn (edgeX M x) i (mid M j') v) ↔ reachIn (edgeX M x) (i + 1) u v := by
      constructor
      · rintro ⟨j', -, -, h1, h2⟩
        exact ⟨mid M j', h1, h2⟩
      · rintro ⟨w, h1, h2⟩
        obtain ⟨j', hj', hmid⟩ := mid_surj M w
        refine ⟨j', Nat.zero_le _, hj', ?_, ?_⟩
        · rw [hmid]; exact h1
        · rw [hmid]; exact h2
    rw [toBool_congr heq] at hk
    exact ⟨1 + k, iterate_trans M x (by rw [Function.iterate_one, rawNext_call_succ]) hk⟩

/-! ### The deterministic machine -/

/-- The Savitch simulator of `M` with recursion depth `K`. -/
