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

lemma qf_of_eigen (H : α → α → ℂ) (ψ : α → ℂ) (E0 : ℝ)
    (heig : ∀ c, ∑ c', H c c' * ψ c' = (E0 : ℂ) * ψ c) :
    qf H ψ = E0 * nrm2 ψ := by
  have h : ∑ c, ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c'
      = ((E0 : ℂ) * ((nrm2 ψ : ℝ) : ℂ)) := by
    rw [nrm2]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ∑ c', (starRingEnd ℂ) (ψ c) * H c c' * ψ c'
        = (starRingEnd ℂ) (ψ c) * ∑ c', H c c' * ψ c' := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c' _ => by ring
    rw [h1, heig c, show (starRingEnd ℂ) (ψ c) * ((E0 : ℂ) * ψ c)
      = (E0 : ℂ) * ((starRingEnd ℂ) (ψ c) * ψ c) by ring, Complex.conj_mul']
  rw [qf, h]
  simp

