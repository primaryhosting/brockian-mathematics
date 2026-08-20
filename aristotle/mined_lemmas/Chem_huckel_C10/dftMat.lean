import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

noncomputable def dftMat : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun j k => chi (j * k)

/-- The inverse discrete Fourier matrix `F⁻¹ j k = ζ ^ (-jk) / 10`. -/
