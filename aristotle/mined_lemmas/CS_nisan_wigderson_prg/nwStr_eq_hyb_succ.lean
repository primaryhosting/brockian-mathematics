import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
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

namespace CS

open Finset

variable {n m : ℕ}

/-- The real value of a boolean: `1` for `true`, `0` for `false`. -/

lemma nwStr_eq_hyb_succ (f : Fin m → (Fin n → Bool) → Bool) (i : Fin m) (x : Fin n → Bool)
    (tail : Fin m → Bool) :
    nwStr f i x tail (f i x) = hyb f ((i : ℕ) + 1) x tail := by
  funext j
  by_cases h : (j : ℕ) < (i : ℕ)
  · simp [nwStr, hyb, h, Nat.lt_succ_of_lt h]
  · by_cases h2 : j = i
    · subst h2; simp [nwStr, hyb]
    · have h3 : ¬ ((j : ℕ) < (i : ℕ) + 1) := by
        have : (j : ℕ) ≠ (i : ℕ) := fun hc => h2 (Fin.ext hc)
        omega
      simp [nwStr, hyb, h, h2, h3]

/-! ### The one-bit prediction identity -/

