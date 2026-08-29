import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma dft_mul_dftInv : dft * dftInv = (13 : ℂ) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : ZMod 13, dft i k * dftInv k j = ee (k * (i - j)) := by
    intro k
    simp only [dft, dftInv, ← ee_add]
    congr 1
    ring
  simp_rw [hterm, sum_ee_mul, sub_eq_zero]
  by_cases h : i = j <;> simp [h]

