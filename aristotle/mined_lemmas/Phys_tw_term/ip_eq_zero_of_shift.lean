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

lemma ip_eq_zero_of_shift (ψ χ : Conf n L → ℂ) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hψ : ∀ c, ψ (sh c) = lam * ψ c) (hχ : ∀ c, χ (sh c) = -(lam * χ c)) :
    ip ψ χ = 0 := by
  have hre : ∑ c, (starRingEnd ℂ) (ψ (sh c)) * χ (sh c) = ip ψ χ :=
    Fintype.sum_bijective sh sh_bijective _ _ (fun c => rfl)
  have hlam2 : (starRingEnd ℂ) lam * lam = 1 := by
    rw [Complex.conj_mul']
    norm_cast
    rw [hlam]; norm_num
  have : ∑ c, (starRingEnd ℂ) (ψ (sh c)) * χ (sh c) = -ip ψ χ := by
    rw [ip, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hψ c, hχ c, map_mul]
    calc (starRingEnd ℂ) lam * (starRingEnd ℂ) (ψ c) * -(lam * χ c)
        = -((starRingEnd ℂ) lam * lam) * ((starRingEnd ℂ) (ψ c) * χ c) := by ring
      _ = -((starRingEnd ℂ) (ψ c) * χ c) := by rw [hlam2]; ring
  rw [hre] at this
  linear_combination this / 2

