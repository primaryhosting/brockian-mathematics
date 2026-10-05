/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma C19_eigenvector (x : ZMod 19) :
    C19.mulVec (fun j => z19 (j * x))
      = (2 * (Real.cos (2 * Real.pi * x.val / 19) : ℂ)) • (fun j => z19 (j * x)) := by
  funext i
  rw [C19_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : (i - 1) * x = i * x + (-x) := by ring
  have e2 : (i + 1) * x = i * x + x := by ring
  rw [e1, e2, z19_add, z19_add, ← z19_add_neg x]
  ring

/-- Every eigenvalue of the adjacency matrix of `C₁₉` is of the form `ζ^k + ζ^(-k)`.
The proof is by discrete Fourier analysis on `ZMod 19`. -/
