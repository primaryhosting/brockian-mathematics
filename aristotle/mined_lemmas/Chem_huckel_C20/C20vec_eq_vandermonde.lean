/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₂₀`, indexed by `Fin 20`
(whose addition is addition modulo `20`). -/

lemma C20vec_eq_vandermonde :
    C20vec = Matrix.vandermonde (fun i : Fin 20 => zeta20 ^ (i : ℕ)) := by
  ext i j
  simp [C20vec, Matrix.vandermonde, ← pow_mul]

