/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Canonical partition function at inverse temperature `β` for energy function `H`. -/

theorem jarzynski_equality (beta : ℝ) (hbeta : beta ≠ 0) (H₀ H₁ : S → ℝ) (T : S ≃ S) :
    ∑ x, boltzmann beta H₀ x * Real.exp (-beta * work H₀ H₁ T x)
      = Real.exp (-beta * (freeEnergy beta H₁ - freeEnergy beta H₀)) := by
  have h0 : (0:ℝ) < partition beta H₀ := partition_pos beta H₀
  have h1 : (0:ℝ) < partition beta H₁ := partition_pos beta H₁
  have hterm : ∀ x : S, boltzmann beta H₀ x * Real.exp (-beta * work H₀ H₁ T x)
      = Real.exp (-beta * H₁ (T x)) / partition beta H₀ := by
    intro x
    unfold boltzmann work
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  have hLHS : ∑ x, boltzmann beta H₀ x * Real.exp (-beta * work H₀ H₁ T x)
      = partition beta H₁ / partition beta H₀ := by
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_div]
    congr 1
    exact T.sum_comp (fun y => Real.exp (-beta * H₁ y))
  rw [hLHS]
  unfold freeEnergy
  have hexp : -beta * (-(1 / beta) * Real.log (partition beta H₁)
      - -(1 / beta) * Real.log (partition beta H₀))
      = Real.log (partition beta H₁) - Real.log (partition beta H₀) := by
    field_simp
    ring
  rw [hexp, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

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

