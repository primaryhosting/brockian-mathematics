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

lemma sum_norm_A_le (H : α → α → ℂ) (ψ : α → ℂ) (M : ℝ)
    (hH : ∀ c c', H c' c = (starRingEnd ℂ) (H c c'))
    (hM : ∀ c, ∑ c', ‖H c c'‖ ≤ M) :
    ∑ c, ∑ c', ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖ ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by
  have hsymm : ∀ c c' : α, ‖H c c'‖ = ‖H c' c‖ := by
    intro c c'; rw [hH c' c]; simp
  have b1 : ∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c‖ ^ 2 ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hM c) (sq_nonneg _)
  have b2 : ∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c'‖ ^ 2 ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c' _ => ?_
    have h : ∑ c : α, ‖H c c'‖ * ‖ψ c'‖ ^ 2 = (∑ c : α, ‖H c' c‖) * ‖ψ c'‖ ^ 2 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by rw [hsymm c c']
    rw [h]
    exact mul_le_mul_of_nonneg_right (hM c') (sq_nonneg _)
  have key : ∀ c c' : α, ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖
      ≤ (‖H c c'‖ * ‖ψ c‖ ^ 2) / 2 + (‖H c c'‖ * ‖ψ c'‖ ^ 2) / 2 := by
    intro c c'
    nlinarith [norm_nonneg (H c c'), sq_nonneg (‖ψ c‖ - ‖ψ c'‖)]
  calc ∑ c, ∑ c', ‖ψ c‖ * ‖H c c'‖ * ‖ψ c'‖
      ≤ ∑ c, ∑ c' : α, ((‖H c c'‖ * ‖ψ c‖ ^ 2) / 2 + (‖H c c'‖ * ‖ψ c'‖ ^ 2) / 2) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => key c c'
    _ = (∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c‖ ^ 2) / 2
          + (∑ c, ∑ c' : α, ‖H c c'‖ * ‖ψ c'‖ ^ 2) / 2 := by
        simp [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ M * ∑ c, ‖ψ c‖ ^ 2 := by linarith

/-- **Twist estimate.**  If every nonzero matrix element of `H` connects configurations whose
twist phases differ (modulo `2π`) by at most `δ`, then the average of the energies of the two
twisted states `e^{±iθ}ψ` exceeds the energy of `ψ` by at most `δ² M ‖ψ‖² / 2`, where `M` bounds
the row sums of `H`. -/
