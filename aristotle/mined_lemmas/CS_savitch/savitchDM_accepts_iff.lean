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


theorem savitchDM_accepts_iff (K : ℕ) :
    (savitchDM M K).Accepts x ↔ reachIn (edgeX M x) K (some M.start) none := by
  obtain ⟨k, hk⟩ := trace_call M x K (some M.start) none []
  have hfin : (rawNext M x)^[k + 1] (Mode.call (some M.start) none K, [])
      = (Mode.done (toBool (reachIn (edgeX M x) K (some M.start) none)), []) := by
    refine iterate_trans M x hk ?_
    rw [Function.iterate_one, rawNext_ret_nil]
  constructor
  · rintro ⟨m, hm⟩
    -- compare the states at time `max m (k+1)`
    have h1 : ((((savitchDM M K).move x)^[m] (savitchDM M K).start)).1.1 = Mode.done true := hm
    have hstart : ((savitchDM M K).start).1 = (Mode.call (some M.start) none K, []) := rfl
    set T := max m (k + 1) with hT
    have hA : (rawNext M x)^[T] (Mode.call (some M.start) none K, [])
        = (Mode.done (toBool (reachIn (edgeX M x) K (some M.start) none)), []) := by
      have : T = (k + 1) + (T - (k + 1)) := by omega
      rw [this, Function.iterate_add_apply, ← show (T - (k+1)) + (k+1) = (k+1) + (T - (k+1)) by
        omega]
      rw [show (rawNext M x)^[k+1] (Mode.call (some M.start) none K, []) = _ from hfin]
      exact iterate_done M x _ _ _
    have hB : ((rawNext M x)^[T] (Mode.call (some M.start) none K, [])).1 = Mode.done true := by
      have : T = m + (T - m) := by omega
      rw [this, Function.iterate_add_apply]
      have hm' : (rawNext M x)^[m] (Mode.call (some M.start) none K, []) =
          (((savitchDM M K).move x)^[m] (savitchDM M K).start).1 := by
        rw [savitchDM_iterate, hstart]
      rw [show (T - m) + m = m + (T - m) by omega] at *
      rw [hm']
      rcases hs : (((savitchDM M K).move x)^[m] (savitchDM M K).start).1 with ⟨md, sst⟩
      have : md = Mode.done true := by rw [← h1, hs]
      subst this
      rw [iterate_done]
    rw [hA] at hB
    simpa using hB
  · intro hreach
    refine ⟨k + 1, ?_⟩
    show ((((savitchDM M K).move x)^[k + 1] (savitchDM M K).start)).1.1 = Mode.done true
    rw [savitchDM_iterate]
    have hstart : ((savitchDM M K).start).1 = (Mode.call (some M.start) none K, []) := rfl
    rw [hstart, hfin]
    simp [hreach]

/-! ### Acceptance of `M` in terms of the configuration graph -/

