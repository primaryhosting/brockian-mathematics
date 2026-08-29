import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

noncomputable def V12 : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.vandermonde (fun i : Fin 12 => om ^ (i : ℕ))

/-- `C12` really is the adjacency matrix of Mathlib's cycle graph on `Fin 12`. -/
