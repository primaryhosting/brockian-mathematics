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

lemma Fin20_add_one_ne_sub_one (i : Fin 20) : i + 1 ≠ i - 1 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin20_add_one_val, Fin20_sub_one_val] at h'
  omega

