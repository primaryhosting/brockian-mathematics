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

lemma spectrum_A20 :
    spectrum ℂ A20 =
      Set.range fun k : ZMod 20 => ((2 * Real.cos (2 * Real.pi * k.val / 20) : ℝ) : ℂ) := by
  have hu : A20 = (dftUnit : Matrix (ZMod 20) (ZMod 20) ℂ) * eigM
      * ((dftUnit⁻¹ : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ) : Matrix (ZMod 20) (ZMod 20) ℂ) := A20_conj
  rw [hu, spectrum.units_conjugate, eigM]
  exact spectrum_diagonal _

/-!
## Main result

The adjacency eigenvalues of the cycle graph `C₂₀` are exactly the `20` Hückel values
`2 cos (2 π k / 20)`, `k = 0, …, 19`.
-/

/-- **Hückel theory for C₂₀.**  The spectrum of the adjacency matrix of the cycle graph `C₂₀`
is exactly `{2 cos (2 π k / 20) : k = 0, 1, …, 19}`.  (In Hückel theory the π-orbital energies are
then `α + β · 2 cos (2 π k / 20)`.) -/
