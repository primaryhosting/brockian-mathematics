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

lemma pow_val_add {a : ℂ} (ha : a ^ 20 = 1) (i j : ZMod 20) :
    a ^ (i + j).val = a ^ i.val * a ^ j.val := by
  rw [ZMod.val_add, pow_mod_twenty ha, pow_add]

/-- The main computation: if `a ^ 20 = 1` then `i ↦ a ^ i.val` is an eigenvector of the
adjacency matrix of `C₂₀` with eigenvalue `a + a⁻¹`. -/
