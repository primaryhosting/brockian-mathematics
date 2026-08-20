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


theorem accepts_iff_reachable :
    M.Accepts x ↔ Relation.ReflTransGen (edgeX M x) (some M.start) none := by
  constructor
  · rintro ⟨s, hs, hacc⟩
    have hlift : ∀ a b : M.S, Relation.ReflTransGen (M.edge x) a b →
        Relation.ReflTransGen (edgeX M x) (some a) (some b) := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih => exact ih.tail hstep
    exact (hlift _ _ hs).tail hacc
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with hnone | ⟨c, hc, hcn⟩
    · exact absurd hnone.symm (by simp)
    · cases c with
      | none => exact absurd hcn id
      | some t =>
        rcases reflTransGen_some_of M x hc M.start rfl with h' | ⟨t', ht', hst'⟩
        · exact absurd h' (by simp)
        · refine ⟨t, ?_, hcn⟩
          rw [Option.some_inj.mp ht'] at hst'
          exact hst'

/-- Savitch's simulation, for a single machine: if the recursion depth `K` is large
enough, the simulator accepts exactly the same inputs as `M`. -/
