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

lemma C20vec_det_ne_zero : C20vec.det ≠ 0 := by
  rw [C20vec_eq_vandermonde]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext (zeta20_primitive.pow_inj i.isLt j.isLt hij)

/-- **Hückel theory for `C₂₀`.** A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₂₀` if and only if `μ = 2 cos (2πk/20)` for some `k = 0,…,19`. -/
