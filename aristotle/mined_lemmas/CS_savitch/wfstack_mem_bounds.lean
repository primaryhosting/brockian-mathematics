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


theorem wfstack_mem_bounds {M : NMachine Sigma} {K : ℕ} :
    ∀ {st : List (Frame M)}, WFstack M K st →
      ∀ (n : ℕ) (f : Frame M), f ∈ st[n]? → f.2.2.1 ≤ K ∧ f.2.2.2.1 < cV M
  | [], _, n, f, hf => by simp at hf
  | (u, v, i, j, ph) :: st, h, n, f, hf => by
      match n with
      | 0 =>
        simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at hf
        subst hf
        refine ⟨?_, h.2.1⟩
        show i ≤ K
        have := h.1
        omega
      | (n + 1) =>
        simp only [List.getElem?_cons_succ] at hf
        exact wfstack_mem_bounds h.2.2 n f hf

