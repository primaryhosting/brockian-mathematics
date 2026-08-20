/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem tail_bound {z : ℕ → ℂ} (hd : Summable fun k => 1 - (z k).re)
    (he : Summable fun k => max 0 (‖z k‖ - 1)) (F : Finset ℕ) (M' : ℝ) (hM'1 : 1 ≤ M')
    (hout : ∀ k, k ∉ F → ‖z k‖ ≤ M') (n : ℕ) (hn : 1 ≤ n) :
    ∑' k : ((F : Set ℕ)ᶜ : Set ℕ), (1 - (z k) ^ n).re
      ≤ 2 * (n : ℝ) ^ 2 * M' ^ n * (∑' k, liMajorant z k) := by
  set c : ℝ := 2 * (n : ℝ) ^ 2 * M' ^ n with hc
  have hc0 : 0 ≤ c := by
    have hM'n : (0 : ℝ) ≤ M' ^ n := pow_nonneg (by linarith) n
    rw [hc]; positivity
  set g : ℕ → ℝ := fun k => c * liMajorant z k with hg
  have hgsum : Summable g := (summable_liMajorant hd he).mul_left c
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg hc0 (liMajorant_nonneg z k)
  have hle : ∀ k : ((F : Set ℕ)ᶜ : Set ℕ), (1 - (z k.1) ^ n).re ≤ g k.1 := by
    rintro ⟨k, hk⟩
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hk
    have hmb := master_bound (z k) n hn
    have hb : (1 - (z k) ^ n).re ≤ |1 - ((z k) ^ n).re| := by
      simp only [Complex.sub_re, Complex.one_re]
      exact le_abs_self _
    refine hb.trans (hmb.trans ?_)
    have hstep : (1 + max 0 (‖z k‖ - 1)) ^ n ≤ M' ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      rcases le_total (‖z k‖) 1 with hcase | hcase
      · rw [max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith)]
        have := hout k hk
        linarith
    have h2 : 2 * (n : ℝ) ^ 2 * (1 + max 0 (‖z k‖ - 1)) ^ n ≤ c := by
      rw [hc]; exact mul_le_mul_of_nonneg_left hstep (by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2 (liMajorant_nonneg z k)
    simpa [hg, liMajorant] using h3
  calc ∑' k : ((F : Set ℕ)ᶜ : Set ℕ), (1 - (z k) ^ n).re
      ≤ ∑' k : ((F : Set ℕ)ᶜ : Set ℕ), g k :=
        Summable.tsum_le_tsum hle ((summable_liTerms hd he n).subtype _) (hgsum.subtype _)
  _ ≤ ∑' k, g k := hgsum.tsum_subtype_le g _ hg0
  _ = 2 * (n : ℝ) ^ 2 * M' ^ n * (∑' k, liMajorant z k) := by rw [hg, tsum_mul_left]

/-- Hard direction: nonnegativity of all Li sums forces all `z k` into the closed unit disc. -/
