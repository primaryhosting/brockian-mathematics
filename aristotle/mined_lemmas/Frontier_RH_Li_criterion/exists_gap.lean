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

theorem exists_gap {z : ℕ → ℂ} (he : Summable fun k => max 0 (‖z k‖ - 1)) {M : ℝ}
    (hM1 : 1 < M) (hMle : ∀ k, ‖z k‖ ≤ M) (hMex : ∃ k, ‖z k‖ = M) :
    ∃ (F : Finset ℕ) (M' : ℝ), F.Nonempty ∧ (∀ k ∈ F, ‖z k‖ = M) ∧ 1 ≤ M' ∧ M' < M ∧
      ∀ k, k ∉ F → ‖z k‖ ≤ M' := by
  set η : ℝ := (M - 1) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hfin := finite_large_norm he hη
  set S : Finset ℕ := hfin.toFinset with hS
  have hmemS : ∀ k, k ∈ S ↔ 1 + η ≤ ‖z k‖ := by
    intro k; rw [hS, Set.Finite.mem_toFinset]; rfl
  obtain ⟨k1, hk1⟩ := hMex
  have hk1S : k1 ∈ S := by rw [hmemS, hk1, hηdef]; linarith
  set F : Finset ℕ := S.filter (fun k => ‖z k‖ = M) with hF
  set G : Finset ℕ := S.filter (fun k => ‖z k‖ ≠ M) with hG
  have hFne : F.Nonempty := ⟨k1, by rw [hF, Finset.mem_filter]; exact ⟨hk1S, hk1⟩⟩
  set Gv : Finset ℝ := insert (1 + η) (G.image fun k => ‖z k‖) with hGv
  have hGvne : Gv.Nonempty := ⟨1 + η, by rw [hGv]; exact Finset.mem_insert_self _ _⟩
  set M' : ℝ := Gv.max' hGvne with hM'
  have hM'mem : M' ∈ Gv := Gv.max'_mem hGvne
  have hηM' : 1 + η ≤ M' := Gv.le_max' _ (by rw [hGv]; exact Finset.mem_insert_self _ _)
  refine ⟨F, M', hFne, ?_, by linarith, ?_, ?_⟩
  · intro k hk; rw [hF, Finset.mem_filter] at hk; exact hk.2
  · rw [hGv, Finset.mem_insert] at hM'mem
    rcases hM'mem with hcase | hcase
    · rw [hcase, hηdef]; linarith
    · rw [Finset.mem_image] at hcase
      obtain ⟨k, hkG, hkv⟩ := hcase
      rw [hG, Finset.mem_filter] at hkG
      exact hkv ▸ lt_of_le_of_ne (hMle k) hkG.2
  · intro k hkF
    by_cases hkS : k ∈ S
    · have hne : ‖z k‖ ≠ M := fun hcontra =>
        hkF (by rw [hF, Finset.mem_filter]; exact ⟨hkS, hcontra⟩)
      have hkG : k ∈ G := by rw [hG, Finset.mem_filter]; exact ⟨hkS, hne⟩
      exact Gv.le_max' _
        (by rw [hGv]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hkG))
    · rw [hmemS] at hkS
      push_neg at hkS
      linarith

/-- The contribution of the indices outside `F` to the Li sum is at most `2 n^2 M'^n T`. -/
