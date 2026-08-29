/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

noncomputable def fcoeff (v : Fin 14 → ℂ) (k : Fin 14) : ℂ :=
  ∑ y : Fin 14, ch (-(k * y)) * v y

/-- Fourier inversion on `Fin 14`. -/
