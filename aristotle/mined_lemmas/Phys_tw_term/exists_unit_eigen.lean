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

lemma exists_unit_eigen (H : α → α → ℂ) (ψ φ : α → ℂ) (E0 : ℝ) (hφ : nrm2 φ ≠ 0)
    (heig : ∀ c, ∑ c', H c c' * φ c' = (E0 : ℂ) * φ c) (horth : ip ψ φ = 0) :
    ∃ χ : α → ℂ, nrm2 χ = 1 ∧ ip ψ χ = 0 ∧ qf H χ = E0 := by
  have hpos : 0 < nrm2 φ := lt_of_le_of_ne (nrm2_nonneg φ) (Ne.symm hφ)
  set t : ℝ := (Real.sqrt (nrm2 φ))⁻¹ with ht
  have htsq : t ^ 2 = (nrm2 φ)⁻¹ := by
    rw [ht, inv_pow, Real.sq_sqrt hpos.le]
  have hnrm : nrm2 (fun c => (t : ℂ) * φ c) = 1 := by
    rw [nrm2_smul, htsq, inv_mul_cancel₀ hφ]
  refine ⟨fun c => (t : ℂ) * φ c, hnrm, ?_, ?_⟩
  · rw [ip] at horth ⊢
    have : ∑ c, (starRingEnd ℂ) (ψ c) * ((t : ℂ) * φ c)
        = (t : ℂ) * ∑ c, (starRingEnd ℂ) (ψ c) * φ c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [this, horth, mul_zero]
  · have heig' : ∀ c, ∑ c', H c c' * ((t : ℂ) * φ c') = (E0 : ℂ) * ((t : ℂ) * φ c) := by
      intro c
      have h2 : ∑ c', H c c' * ((t : ℂ) * φ c') = (t : ℂ) * ∑ c', H c c' * φ c' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c' _ => by ring
      rw [h2, heig c]; ring
    rw [qf_of_eigen H _ E0 heig', hnrm, mul_one]

end Abstract

/-! ## Part II: the half-integer spin chain

Sites are labelled by `ZMod L` (a periodic chain of `L` sites), each site carrying `n = 2S+1`
states.  Half-integral spin `S` means exactly that `n` is even.  Configurations `Conf n L`
form a basis of the Hilbert space, so states are functions `Conf n L → ℂ`.
-/

section Chain

/-- Spin configurations of a periodic chain of `L` sites with `n` states per site. -/
abbrev Conf (n L : ℕ) := ZMod L → Fin n

variable {n L : ℕ} [NeZero L]

/-- Twice the `z`-component of the spin of a site in state `k`, for local dimension `n = 2S+1`;
the spin `S = (n-1)/2` is half-integral exactly when `n` is even. -/
