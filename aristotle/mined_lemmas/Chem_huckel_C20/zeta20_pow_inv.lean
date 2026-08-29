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

lemma zeta20_pow_inv (m : ℕ) : zeta20 ^ (19 * m) = (zeta20 ^ m)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, show 19 * m + m = 20 * m by ring, pow_mul, zeta20_pow_twenty, one_pow]

