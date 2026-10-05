/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma chi_step (m : ℤ) (i : Fin 15) : chi m (i + 1) = chi m i * W m := by
  rw [chi, chi, ← W_add]
  refine W_congr ?_
  obtain ⟨t, ht⟩ := fin_succ_dvd i
  refine ⟨m * t, ?_⟩
  have : (((i + 1 : Fin 15) : ℕ) : ℤ) = (i : ℕ) + 1 + 15 * t := by omega
  rw [this]; ring

