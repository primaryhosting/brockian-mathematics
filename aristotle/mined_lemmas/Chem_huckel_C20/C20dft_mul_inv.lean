/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20dft_mul_inv : C20dft * C20dftInv = (20 : ℂ) • (1 : Matrix (ZMod 20) (ZMod 20) ℂ) := by
  ext i j
  have hterm : ∀ k : ZMod 20, C20dft i k * C20dftInv k j
      = (C20root i * (C20root j)⁻¹) ^ k.val := by
    intro k
    rw [C20dft, C20dftInv, C20vec_eq, C20root_symm i k, mul_pow, ← inv_pow]
  have hb : (C20root i * (C20root j)⁻¹) ^ 20 = 1 := by
    rw [mul_pow, inv_pow, C20root_pow_twenty, C20root_pow_twenty, inv_one, mul_one]
  rw [Matrix.mul_apply]
  simp only [hterm]
  rw [sum_pow_val hb]
  rcases eq_or_ne i j with h | h
  · subst h
    rw [if_pos (mul_inv_cancel₀ (C20root_ne_zero i))]
    simp
  · rw [if_neg, Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero]
    intro hcon
    refine h (C20root_inj ?_)
    have hj := C20root_ne_zero j
    field_simp at hcon
    exact hcon

