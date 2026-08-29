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

lemma tw_sh_of_odd (ψ : Conf n L → ℂ) (θ' : Conf n L → ℝ)
    (hodd : ∀ c, ψ c ≠ 0 → ∃ m : ℤ, θ' (sh c) - θ' c = Real.pi * (2 * m + 1))
    (lam : ℂ) (hψ : ∀ c, ψ (sh c) = lam * ψ c) (c : Conf n L) :
    tw θ' ψ (sh c) = -(lam * tw θ' ψ c) := by
  by_cases hc : ψ c = 0
  · simp [tw, hψ c, hc]
  · obtain ⟨m, hm⟩ := hodd c hc
    have hsplit : ((θ' (sh c) : ℝ) : ℂ) * Complex.I
        = ((Real.pi * (2 * m + 1) : ℝ) : ℂ) * Complex.I + ((θ' c : ℝ) : ℂ) * Complex.I := by
      have : (θ' (sh c) : ℝ) = Real.pi * (2 * m + 1) + θ' c := by linarith [hm]
      rw [this]; push_cast; ring
    simp only [tw, hψ c, hsplit, Complex.exp_add, exp_pi_odd]
    ring

/-- Two translation eigenstates with opposite translation eigenvalues are orthogonal. -/
