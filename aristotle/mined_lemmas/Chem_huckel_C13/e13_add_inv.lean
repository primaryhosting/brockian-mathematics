import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma e13_add_inv (k : ZMod 13) :
    e13 k + (e13 k)⁻¹ = ((huckelEigenvalue k.val : ℝ) : ℂ) := by
  rw [e13_eq_exp, ← Complex.exp_neg, huckelEigenvalue]
  push_cast
  rw [Complex.cos, ← neg_mul]
  ring

/-- The Fourier characters are eigenvectors of the adjacency matrix. -/
