import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- Real-valued indicator of a Boolean value. -/

lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]

/-- Averaging over an updated coordinate: summing `F` over all strings with the `i`-th
coordinate overwritten by `b`, for both values of `b`, doubles the total sum. -/
