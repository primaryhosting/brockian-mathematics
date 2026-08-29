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

lemma qf_tw_identity (H : α → α → ℂ) (θ : α → ℝ) (ψ : α → ℂ) :
    qf H (tw θ ψ) + qf H (tw (fun c => -θ c) ψ)
      = 2 * qf H ψ + (∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
          * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c')).re := by
  have hsum : (∑ c, ∑ c', (starRingEnd ℂ) (tw θ ψ c) * H c c' * tw θ ψ c')
      + (∑ c, ∑ c', (starRingEnd ℂ) (tw (fun c => -θ c) ψ c) * H c c' * tw (fun c => -θ c) ψ c')
      = 2 * (∑ c, ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c')
        + ∑ c, ∑ c', ((2 * Real.cos (θ c' - θ c) - 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (ψ c) * H c c' * ψ c') := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    show (starRingEnd ℂ) (Complex.exp ((θ c : ℂ) * Complex.I) * ψ c) * H c c' *
        (Complex.exp ((θ c' : ℂ) * Complex.I) * ψ c')
      + (starRingEnd ℂ) (Complex.exp (((-θ c : ℝ) : ℂ) * Complex.I) * ψ c) * H c c' *
        (Complex.exp (((-θ c' : ℝ) : ℂ) * Complex.I) * ψ c') = _
    rw [tw_term, tw_term, show ((-θ c' : ℝ) - (-θ c : ℝ)) = -(θ c' - θ c) by ring, ← add_mul,
      two_cos]
    push_cast
    ring
  calc qf H (tw θ ψ) + qf H (tw (fun c => -θ c) ψ) = _ := by
        rw [qf, qf, ← Complex.add_re, hsum]
    _ = _ := by rw [Complex.add_re, Complex.mul_re]; simp [qf]

