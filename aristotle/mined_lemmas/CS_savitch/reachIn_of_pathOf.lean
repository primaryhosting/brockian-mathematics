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


theorem reachIn_of_pathOf : ∀ (i l : ℕ) (u v : V), PathOf E l u v → l ≤ 2 ^ i →
    reachIn E i u v := by
  intro i
  induction i with
  | zero =>
    rintro l u v ⟨p, hp0, hpl, hstep⟩ hl
    simp only [pow_zero] at hl
    interval_cases l
    · exact Or.inl (by rw [← hp0, ← hpl])
    · refine Or.inr ?_
      have := hstep 0 (by norm_num)
      rw [hp0] at this
      simpa [hpl] using this
  | succ i ih =>
    rintro l u v ⟨p, hp0, hpl, hstep⟩ hl
    by_cases hle : l ≤ 2 ^ i
    · exact reachIn_succ_of i (ih l u v ⟨p, hp0, hpl, hstep⟩ hle)
    · have hgt : 2 ^ i < l := by omega
      refine ⟨p (2 ^ i), ?_, ?_⟩
      · exact ih (2 ^ i) u (p (2 ^ i)) ⟨p, hp0, rfl, fun j hj => hstep j (by omega)⟩ le_rfl
      · refine ih (l - 2 ^ i) (p (2 ^ i)) v
          ⟨fun j => p (2 ^ i + j), rfl, ?_, fun j hj => ?_⟩ ?_
        · have h1 : 2 ^ i + (l - 2 ^ i) = l := by omega
          simp only [h1, hpl]
        · have := hstep (2 ^ i + j) (by omega)
          simpa [Nat.add_assoc] using this
        · have h2 : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
          omega

/-- Reachability yields a walk. -/
