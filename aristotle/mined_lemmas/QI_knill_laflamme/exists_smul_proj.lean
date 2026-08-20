/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/

lemma exists_smul_proj {P : Matrix d d ℂ} (hPi : P * P = P) (hP0 : P ≠ 0)
    {M : Matrix d d ℂ} (h : ∀ ψ : d → ℂ, P *ᵥ ψ = ψ → ∃ t : ℂ, M *ᵥ ψ = t • ψ) :
    ∃ t : ℂ, M * P = t • P := by
  obtain ⟨v₀, hv₀⟩ := exists_mulVec_ne_zero hP0
  have hu₀ : P *ᵥ (P *ᵥ v₀) = P *ᵥ v₀ := by rw [mulVec_mulVec, hPi]
  obtain ⟨t₀, ht₀⟩ := h (P *ᵥ v₀) hu₀
  refine ⟨t₀, ext_iff_mulVec.mpr fun v => ?_⟩
  rw [← mulVec_mulVec, smul_mulVec]
  set u := P *ᵥ v with hudef
  have hu : P *ᵥ u = u := by rw [hudef, mulVec_mulVec, hPi]
  rcases eq_or_ne u 0 with h0 | h0
  · rw [h0]; simp
  obtain ⟨t, ht⟩ := h u hu
  suffices ht0 : t = t₀ by rw [ht, ht0]
  obtain ⟨s, hs⟩ := h (u + P *ᵥ v₀) (by rw [mulVec_add, hu, hu₀])
  rw [mulVec_add, ht, ht₀, smul_add] at hs
  have hkey : (t - s) • u = (s - t₀) • (P *ᵥ v₀) := by
    rw [sub_smul, sub_smul]
    linear_combination (norm := module) hs
  rcases eq_or_ne s t₀ with hst | hst
  · rw [hst, sub_self, zero_smul] at hkey
    rcases smul_eq_zero.mp hkey with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 h0
  · have hne : s - t₀ ≠ 0 := sub_ne_zero.mpr hst
    have hv0eq : P *ᵥ v₀ = ((t - s) / (s - t₀)) • u := by
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have h1 : M *ᵥ (P *ᵥ v₀) = t • (P *ᵥ v₀) := by
      rw [hv0eq, mulVec_smul, ht, smul_smul, smul_smul, mul_comm]
    rw [ht₀] at h1
    have h4 := sub_eq_zero.mpr h1.symm
    rw [← sub_smul] at h4
    rcases smul_eq_zero.mp h4 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hv₀

omit [DecidableEq ι] in
