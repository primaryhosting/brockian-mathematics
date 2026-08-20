/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma ec_add_inv (k : Fin 20) :
    ec k + (ec k)⁻¹ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) := by
  have hexp : ec k = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    simp only [ec, zeta20]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (ec k)⁻¹ = Complex.exp (-((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [hexp, ← Complex.exp_neg]
    congr 1
    ring
  rw [hinv, hexp, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

/-! ### The Fourier (Vandermonde) matrix diagonalising the circulant -/

/-- The discrete Fourier matrix `F j k = ζ^{jk}`. -/
