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

lemma C20vec_ne_zero (k : ZMod 20) : C20vec k ≠ 0 := by
  intro h
  have h0 : C20vec k 0 = 0 := by rw [h]; rfl
  rw [C20vec_eq] at h0
  simp only [show (0 : ZMod 20).val = 0 from rfl, pow_zero] at h0
  exact one_ne_zero h0

/-! ### The full spectrum -/

