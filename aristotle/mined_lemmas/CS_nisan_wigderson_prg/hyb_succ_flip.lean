import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/

lemma hyb_succ_flip {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) (x : Fin n → Bool) (r : Fin m → Bool) :
    hyb S f (k + 1) x (Function.update r i (!(r i))) = hyb S f (k + 1) x r := by
  funext j
  simp only [hyb]
  by_cases h : (j : ℕ) < k + 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hj : j ≠ i := fun e => by subst e; omega
    rw [Function.update_of_ne hj]

