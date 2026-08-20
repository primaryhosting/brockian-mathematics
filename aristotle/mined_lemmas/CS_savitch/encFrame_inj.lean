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


theorem encFrame_inj {M : NMachine Sigma} {K : ℕ} {f g : Frame M}
    (hf : f.2.2.1 ≤ K ∧ f.2.2.2.1 < cV M) (hg : g.2.2.1 ≤ K ∧ g.2.2.2.1 < cV M)
    (h : encFrame M K f = encFrame M K g) : f = g := by
  obtain ⟨u, v, i, j, ph⟩ := f
  obtain ⟨u', v', i', j', ph'⟩ := g
  simp only [encFrame, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at hf hg
  have : i = i' := by omega
  have : j = j' := by omega
  simp_all

/-- Encoding of modes. -/
