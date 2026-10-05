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

lemma sum_pow_val {b : ℂ} (hb : b ^ 20 = 1) :
    ∑ k : ZMod 20, b ^ k.val = if b = 1 then 20 else 0 := by
  have h0 : ∑ k : ZMod 20, b ^ k.val = ∑ n ∈ Finset.range 20, b ^ n :=
    Fin.sum_univ_eq_sum_range (fun n => b ^ n) 20
  rw [h0]
  by_cases h : b = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hb]
    simp

/-- The (unnormalized) discrete Fourier matrix, whose `k`-th column is `C20vec k`. -/
