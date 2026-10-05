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

lemma zeta20_primitive : IsPrimitiveRoot zeta20 20 := by
  have := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [zeta20] using this

