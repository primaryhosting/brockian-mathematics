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

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma qf_tw_add_le (H : α → α → ℂ) (θ : α → ℝ) (ψ : α → ℂ) (δ M : ℝ)
    (hH : ∀ c c', H c' c = (starRingEnd ℂ) (H c c'))
    (hflux : ∀ c c', H c c' ≠ 0 → ∃ k : ℤ, |θ c' - θ c - 2 * Real.pi * k| ≤ δ)
    (hM : ∀ c, ∑ c', ‖H c c'‖ ≤ M) :
    qf H (tw θ ψ) + qf H (tw (fun c => -θ c) ψ)
      ≤ 2 * qf H ψ + δ ^ 2 * (M * ∑ c, ‖ψ c‖ ^ 2) := by
  rw [qf_tw_identity]
  have hre : (∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
      * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')).re
      ≤ δ ^ 2 * (M * ∑ c, ‖ψ c‖ ^ 2) := by
    calc (∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')).re
        ≤ ‖∑ c, ∑ c' : α, ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')‖ := Complex.re_le_norm _
      _ ≤ ∑ c, ∑ c' : α, ‖((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')‖ :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun c _ => norm_sum_le _ _)
      _ ≤ ∑ c, ∑ c' : α, δ ^ 2 * (‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖) := by
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
          by_cases hz : H c c' = 0
          · simp [hz]
          · obtain ⟨k, hk⟩ := hflux c c' hz
            have hb : |2 * Real.cos (θ c' - θ c) - 2| ≤ δ ^ 2 := cos_bound hk
            rw [norm_mul]
            have h1 : ‖(((2 * Real.cos (θ c' - θ c) - 2 : ℝ)) : ℂ)‖ ≤ δ ^ 2 := by
              rw [Complex.norm_real]; exact hb
            have h2 : ‖(starRingEnd ℂ) (ψ c) * H c c' * ψ c'‖ = ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖ := by
              simp
            rw [h2]
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = δ ^ 2 * ∑ c, ∑ c' : α, ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
      _ ≤ δ ^ 2 * (M * ∑ c, ‖ψ c‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_norm_A_le H ψ M hH hM) (sq_nonneg _)
  linarith

