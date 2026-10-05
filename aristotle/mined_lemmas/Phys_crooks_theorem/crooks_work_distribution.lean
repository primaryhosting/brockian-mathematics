import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/

theorem crooks_work_distribution {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (R : Γ → Γ) (hR : Function.Involutive R) (W : Γ → ℝ) (hW : ∀ g, W (R g) = -W g)
    (pF pR : Γ → ℝ) (beta dF w : ℝ)
    (h : ∀ g, pF g = Real.exp (beta * (W g - dF)) * pR (R g)) :
    ∑ g ∈ Finset.univ.filter (fun g => W g = w), pF g
      = Real.exp (beta * (w - dF)) *
          ∑ g ∈ Finset.univ.filter (fun g => W g = -w), pR g := by
  classical
  have step1 : ∑ g ∈ Finset.univ.filter (fun g => W g = w), pF g
      = Real.exp (beta * (w - dF)) *
        ∑ g ∈ Finset.univ.filter (fun g => W g = w), pR (R g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g hg
    simp only [Finset.mem_filter] at hg
    rw [h g, hg.2]
  rw [step1]
  congr 1
  refine Finset.sum_nbij' (fun g => R g) (fun g => R g) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [hW, hg]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [hW, hg]; ring
  · intro g _; exact hR g
  · intro g _; exact hR g
  · intro g _; rfl

end Phys

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

