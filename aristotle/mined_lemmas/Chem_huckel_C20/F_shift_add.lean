import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma F_shift_add (j k : Fin 20) : F (j + 1) k = F j k * w ^ (k : ℕ) := by
  have hv : ((j + 1 : Fin 20) : ℕ) = ((j : ℕ) + 1) % 20 := by
    simp [Fin.val_add]
  have hcong : ((j : ℕ) + 1) % 20 * (k : ℕ) ≡ ((j : ℕ) + 1) * (k : ℕ) [MOD 20] :=
    Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  rw [F, F, hv, w_pow_congr hcong, ← pow_add]
  congr 1
  ring

