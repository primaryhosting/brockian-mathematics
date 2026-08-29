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

lemma zeta20_pow_mod (a : ℕ) : zeta20 ^ a = zeta20 ^ (a % 20) := by
  conv_lhs => rw [← Nat.div_add_mod a 20]
  rw [pow_add, pow_mul, zeta20_pow_twenty, one_pow, one_mul]

