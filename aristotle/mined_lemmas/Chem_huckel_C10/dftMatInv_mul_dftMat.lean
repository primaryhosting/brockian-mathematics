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

lemma dftMatInv_mul_dftMat : dftMatInv * dftMat = 1 :=
  mul_eq_one_comm.mp dftMat_mul_dftMatInv

/-- The Fourier matrix as a unit of the matrix ring. -/
