/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

noncomputable def C20dftUnit : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ :=
  ⟨C20dft, (20 : ℂ)⁻¹ • C20dftInv, C20dft_mul_inv_one,
    mul_eq_one_comm.mp C20dft_mul_inv_one⟩

/-- The characteristic polynomial of the adjacency matrix of `C₂₀` factors as
`∏ₖ (X - 2 cos (2πk/20))`: the eigenvalues are exactly the `2 cos (2πk/20)`,
with multiplicity. -/
