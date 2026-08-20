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

lemma dftM_mul_dftInvM : dftM * dftInvM = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 20, dftM j k * dftInvM k l = (20 : ℂ)⁻¹ * w ((j - l) * k) := by
    intro k
    simp only [dftM, dftInvM, Matrix.of_apply]
    rw [show (j - l) * k = j * k + -(k * l) by ring, w_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.mul_sum, w_sum]
  by_cases hjl : j = l
  · subst hjl; simp
  · rw [if_neg (by simpa [sub_eq_zero] using hjl), Matrix.one_apply_ne hjl]
    ring

