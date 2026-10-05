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

lemma flip_involutive {m : ℕ} (i : Fin m) :
    Function.Involutive (fun r : Fin m → Bool => Function.update r i (!(r i))) := by
  intro r
  simp only [Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]

