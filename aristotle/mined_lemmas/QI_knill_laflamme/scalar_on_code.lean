/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem scalar_on_code {P : Matrix n n ℂ} {T : Matrix n n ℂ}
    (h : ∀ v : n → ℂ, P *ᵥ v = v → ip v v = 1 → ∃ c : ℂ, T *ᵥ v = c • v) :
    ∃ c : ℂ, ∀ v : n → ℂ, P *ᵥ v = v → T *ᵥ v = c • v := by
  -- a scalar for every nonzero code vector
  have key : ∀ v : n → ℂ, P *ᵥ v = v → v ≠ 0 → ∃ c : ℂ, T *ᵥ v = c • v := by
    intro v hv hv0
    obtain ⟨r, hr, hru⟩ := exists_unit_smul hv0
    obtain ⟨c, hc⟩ := h (r • v) (by rw [mulVec_smul, hv]) hru
    exact ⟨c, scalar_of_unit_scalar hr hc⟩
  by_cases hex : ∃ v : n → ℂ, P *ᵥ v = v ∧ v ≠ 0
  · obtain ⟨v₀, hv₀, hv₀0⟩ := hex
    obtain ⟨c₀, hc₀⟩ := key v₀ hv₀ hv₀0
    refine ⟨c₀, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · simp [hv0]
    obtain ⟨cv, hcv⟩ := key v hv hv0
    by_cases hsum : v + v₀ = 0
    · have : v = (-1 : ℂ) • v₀ := by
        have : v = -v₀ := by linear_combination (norm := module) hsum
        rw [this]; module
      rw [this, mulVec_smul, hc₀, smul_comm]
    · obtain ⟨cw, hcw⟩ := key (v + v₀) (by rw [mulVec_add, hv, hv₀]) hsum
      rw [mulVec_add, hcv, hc₀] at hcw
      -- (cv - cw) • v = (cw - c₀) • v₀
      have hkey : (cv - cw) • v = (cw - c₀) • v₀ := by
        linear_combination (norm := module) hcw
      by_cases hcc : cv = cw
      · rw [hcc, sub_self, zero_smul] at hkey
        have : cw - c₀ = 0 := by
          by_contra hne
          exact hv₀0 (by
            have := congrArg (fun x => (cw - c₀)⁻¹ • x) hkey.symm
            simpa [smul_smul, inv_mul_cancel₀ hne] using this)
        rw [hcv, hcc, sub_eq_zero.1 this]
      · have hne : cv - cw ≠ 0 := sub_ne_zero.2 hcc
        have hvv : v = ((cw - c₀) / (cv - cw)) • v₀ := by
          have := congrArg (fun x => (cv - cw)⁻¹ • x) hkey
          simpa [smul_smul, inv_mul_cancel₀ hne, div_eq_inv_mul] using this
        rw [hvv, mulVec_smul, hc₀, smul_comm]
  · push_neg at hex
    refine ⟨0, fun v hv => ?_⟩
    rw [hex v hv]
    simp

omit [DecidableEq n] in
/-- Matrix elements of a "sandwiched" product. -/
