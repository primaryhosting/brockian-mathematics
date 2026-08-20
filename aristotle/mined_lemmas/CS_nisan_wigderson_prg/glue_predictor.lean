/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

lemma glue_predictor {n m ℓ d : ℕ} {S : Fin m → Fin n → Fin ℓ}
    (hSinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      (univ.filter fun k : Fin n => ∃ k', S j k' = S i k).card ≤ d)
    (f : (Fin n → Bool) → Bool) (D : (Fin m → Bool) → Bool) {t : ℕ} (ht : t < m)
    (c : (Fin m → Bool) → Bool) :
    ∃ g : (Fin n → Bool) → Bool, IsNWPredictor d D t g ∧
      (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
          (xor (c p.2) (D (hyb S f t p.1 p.2)) == nwGen S f p.1 ⟨t, ht⟩))
        ≤ pr fun z => g z == f z := by
  set it : Fin m := ⟨t, ht⟩ with hit
  set σ : Fin n → Fin ℓ := S it with hσdef
  set Φ : (Fin ℓ → Bool) → (Fin m → Bool) → ℝ :=
    fun x y => ind (xor (c y) (D (hyb S f t x y)) == nwGen S f x it) with hΦ
  have hLHS : (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
          (xor (c p.2) (D (hyb S f t p.1 p.2)) == nwGen S f p.1 it))
      = 𝔼 (x : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), Φ x y := pr_prod _
  have hswap : (𝔼 (x : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), Φ x y)
      = 𝔼 (x0 : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y := by
    rw [expect_glue (hSinj it) fun x => 𝔼 (y : Fin m → Bool), Φ x y]
    rw [Finset.expect_comm]
    refine Finset.expect_congr rfl fun x0 _ => ?_
    exact Finset.expect_comm _ _ _
  obtain ⟨x0, hx0⟩ := exists_ge_expect
    (fun x0 : Fin ℓ → Bool => 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
  obtain ⟨y, hy⟩ := exists_ge_expect
    (fun y : Fin m → Bool => 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
  refine ⟨fun z => xor (c y) (D (hyb S f t (glue σ z x0) y)), ?_, ?_⟩
  · refine ⟨fun j z => if (j : ℕ) < t then f (fun k => glue σ z x0 (S j k)) else false,
      y, c y, ?_, ?_⟩
    · intro j
      by_cases hj : (j : ℕ) < t
      · refine ⟨univ.filter fun k : Fin n => ∃ k', S j k' = σ k, ?_, ?_⟩
        · refine hdesign it j ?_
          intro hcon
          rw [← hcon] at hj
          exact absurd hj (lt_irrefl t)
        · intro z z' hzz
          simp only [hj, if_true]
          congr 1
          funext k'
          by_cases hmem : ∃ k, σ k = S j k'
          · obtain ⟨k, hk⟩ := hmem
            rw [← hk, glue_apply_mem (hSinj it), glue_apply_mem (hSinj it)]
            refine hzz k ?_
            simp only [mem_filter, mem_univ, true_and]
            exact ⟨k', hk.symm⟩
          · push_neg at hmem
            rw [glue_apply_not_mem _ _ hmem, glue_apply_not_mem _ _ hmem]
      · exact ⟨∅, by simp, by intro z z' _; simp [hj]⟩
    · intro z
      have hh : (hyb S f t (glue σ z x0) y)
          = fun j : Fin m => if (j : ℕ) < t then
              (if (j : ℕ) < t then f (fun k => glue σ z x0 (S j k)) else false) else y j := by
        funext j
        by_cases hj : (j : ℕ) < t <;> simp [hyb, hj, nwGen]
      simp only
      rw [hh]
  · have hkey : (𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
        = pr fun z => (xor (c y) (D (hyb S f t (glue σ z x0) y))) == f z := by
      unfold pr
      refine Finset.expect_congr rfl fun z _ => ?_
      simp only [hΦ]
      congr 2
      show nwGen S f (glue σ z x0) it = f z
      simp only [nwGen]
      congr 1
      funext k
      exact glue_apply_mem (hSinj it) z x0 k
    rw [hLHS, hswap]
    calc (𝔼 (x0 : Fin ℓ → Bool), 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y)
        ≤ 𝔼 (y : Fin m → Bool), 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y := hx0
      _ ≤ 𝔼 (z : Fin n → Bool), Φ (glue σ z x0) y := hy
      _ = _ := hkey

/-- Combination of the two previous steps: a hybrid gap of `δ` at step `t` yields a
Nisan–Wigderson predictor for `f` with advantage `δ`. -/
