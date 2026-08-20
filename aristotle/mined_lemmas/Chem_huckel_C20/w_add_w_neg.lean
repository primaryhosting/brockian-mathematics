/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as an ordinary block comment.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Finset Matrix

/-!
## Setup

In Hückel theory for the (hypothetical) monocyclic annulene `C₂₀`, the π-system Hamiltonian is
`α • I + β • A`, where `A` is the adjacency matrix of the cycle graph `C₂₀`.  Thus the Hückel
spectrum is determined by the adjacency spectrum of `C₂₀`, which we compute here.

The index type `Fin 20` of `SimpleGraph.cycleGraph 20` is definitionally `ZMod 20`, and we use the
ring structure of `ZMod 20` throughout, so that the adjacency matrix is a circulant matrix which is
diagonalised by the discrete Fourier transform matrix.
-/

/-- The standard additive character `w m = exp (2 π i m / 20)` on `ZMod 20`. -/

lemma w_add_w_neg (l : ZMod 20) :
    w l + w (-l) = ((2 * Real.cos (2 * Real.pi * l.val / 20) : ℝ) : ℂ) := by
  set t : ℂ := ((2 * Real.pi * l.val / 20 : ℝ) : ℂ) with ht
  have h1 : w l = Complex.exp (t * Complex.I) := w_eq l
  have hexp : Complex.exp (t * Complex.I) * Complex.exp (-(t * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have h2 : w (-l) = Complex.exp (-t * Complex.I) := by
    have hmul := w_mul_w_neg l
    rw [h1] at hmul
    refine mul_left_cancel₀ (Complex.exp_ne_zero (t * Complex.I)) ?_
    rw [hmul, neg_mul, hexp]
  have hcos : ((2 * Real.cos (2 * Real.pi * l.val / 20) : ℝ) : ℂ) = 2 * Complex.cos t := by
    rw [ht]; push_cast [Complex.ofReal_cos]; ring
  rw [h1, h2, hcos, Complex.two_cos]

/-- The adjacency matrix of the cycle `C₂₀`, written as a circulant matrix over `ZMod 20`. -/
