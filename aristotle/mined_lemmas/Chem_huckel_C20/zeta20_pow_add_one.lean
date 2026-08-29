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

lemma zeta20_pow_add_one (i k : Fin 20) :
    zeta20 ^ ((i + 1).val * k.val) = zeta20 ^ ((i.val + 1) * k.val) := by
  rw [zeta20_pow_mod, zeta20_pow_mod ((i.val + 1) * k.val), Fin20_add_one_val]
  exact congrArg _ ((Nat.mod_modEq (i.val + 1) 20).mul_right k.val)

