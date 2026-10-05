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

lemma hyb_eq_update {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) (x : Fin n → Bool) (r : Fin m → Bool) :
    hyb S f k x r = Function.update (hyb S f (k + 1) x r) i (r i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [hyb, hi]
  · have hjk : (j : ℕ) ≠ k := fun h => hj (Fin.ext (h.trans hi.symm))
    rw [Function.update_of_ne hj]
    simp only [hyb]
    by_cases h : (j : ℕ) < k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

