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

noncomputable def zeta20 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

/-- The matrix whose `k`-th column is the eigenvector `i ↦ ζ^(ik)`. -/
