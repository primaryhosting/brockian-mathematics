/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ### A primitive 7th root of unity -/

/-- A primitive 7th root of unity. -/

lemma dft7_shift (a i k : Fin 7) : dft7 (i + a) k = w7 ^ ((i : ℕ) * (k : ℕ) + (a : ℕ) * (k : ℕ)) := by
  rw [dft7_apply]
  refine w7_pow_congr ?_
  have hv : ((i + a : Fin 7) : ℕ) = ((i : ℕ) + (a : ℕ)) % 7 := by simp [Fin.val_add]
  rw [hv]
  have h : ((((i : ℕ) + (a : ℕ)) % 7) * (k : ℕ)) % 7 = (((i : ℕ) + (a : ℕ)) * (k : ℕ)) % 7 :=
    (Nat.mod_modEq _ 7).mul_right _
  rw [h]
  congr 1
  ring

/-! ### The adjacency matrix of `C₇` acting on a vector -/

