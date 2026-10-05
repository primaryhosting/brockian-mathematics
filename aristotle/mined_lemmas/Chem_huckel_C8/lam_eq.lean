import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including this
module docstring, so the header comment appears immediately after the single import.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₈`, over `ℂ`. -/

lemma lam_eq (k : Fin 8) : lam k = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) : ℝ) := by
  have hchi : chi k = Complex.exp ((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I) := by
    simp only [chi, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hchi' : chi (-k) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I)) := by
    rw [chi_neg, hchi, ← Complex.exp_neg]
  rw [lam, hchi, hchi']
  rw [Complex.ofReal_mul, Complex.ofReal_cos]
  rw [Complex.cos]
  push_cast
  ring_nf

/-- The (Vandermonde/DFT) matrix diagonalizing the adjacency matrix. -/
