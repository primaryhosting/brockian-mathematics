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

lemma A20_mul_dftM : A20 * dftM = dftM * eigM := by
  ext i l
  have hne : (i - 1 : ZMod 20) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination -h
    revert h2; decide
  have hstep : ∀ j : ZMod 20, A20 i j * dftM j l
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 20)) then dftM j l else 0 := by
    intro j
    have e1 : (i - j = 1) ↔ j = i - 1 := by constructor <;> intro h <;> linear_combination -h
    have e2 : (j - i = 1) ↔ j = i + 1 := by constructor <;> intro h <;> linear_combination h
    simp only [A20, Matrix.of_apply, Finset.mem_insert, Finset.mem_singleton, e1, e2]
    split_ifs <;> simp
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_pair hne, eigM, Matrix.mul_diagonal]
  simp only [dftM, Matrix.of_apply]
  rw [show (i - 1) * l = i * l + -l by ring, show (i + 1) * l = i * l + l by ring, w_add, w_add,
    ← mul_add, add_comm (w (-l)) (w l), w_add_w_neg]

/-- `C₂₀`'s adjacency matrix is conjugate to the diagonal matrix of Hückel eigenvalues. -/
