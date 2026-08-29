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

lemma hyb_apply_self {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (k : ℕ) (i : Fin m) (hi : (i : ℕ) = k) (x : Fin n → Bool) (r : Fin m → Bool) :
    hyb S f (k + 1) x r i = f (fun t => x (S i t)) := by
  simp [hyb, hi]

/-- The success indicator of the next-bit predictor built from the distinguisher `D`
at hybrid `k`: it predicts the `i`-th output bit `f (x ∘ S i)` from the earlier bits. -/
