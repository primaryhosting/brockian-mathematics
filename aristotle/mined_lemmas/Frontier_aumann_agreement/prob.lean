import RequestProject.Main

/-! Sanity checks for `Frontier.aumann_agreement`: the hypotheses are satisfiable by a
concrete example with two genuinely different information partitions. -/

example : (1 : ℝ) = 1 :=
  Frontier.aumann_agreement (Ω := Bool) (fun _ => (1 : ℝ) / 2) Finset.univ
    (fun _ => Finset.univ) (fun ω => {ω})
    (fun _ => Finset.mem_univ _) (fun _ _ _ => rfl)
    (fun _ => Finset.mem_singleton_self _)
    (fun _ _ h => by simp only [Finset.mem_singleton] at h; subst h; rfl)
    Finset.univ (fun _ _ => Finset.subset_univ _) (fun _ _ => Finset.subset_univ _)
    (by norm_num [Frontier.prob, Fintype.sum_bool]) 1 1
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])

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

namespace Frontier

/-- The prior probability (mass) that the common prior `p` assigns to a finite event `s`. -/

noncomputable def prob {Ω : Type*} (p : Ω → ℝ) (s : Finset Ω) : ℝ := ∑ x ∈ s, p x

