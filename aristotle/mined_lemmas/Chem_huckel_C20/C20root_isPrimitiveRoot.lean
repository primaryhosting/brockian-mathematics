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

lemma C20root_isPrimitiveRoot : IsPrimitiveRoot (C20root 1) 20 := by
  have h : C20root 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((20 : ℕ) : ℂ)) := by
    rw [C20root]
    congr 1
    push_cast [show (1 : ZMod 20).val = 1 from rfl]
    ring
  rw [h]
  exact Complex.isPrimitiveRoot_exp 20 (by norm_num)

