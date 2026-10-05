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

lemma sum_flip {m : ℕ} (i : Fin m) (G : (Fin m → Bool) → ℝ) :
    ∑ r : Fin m → Bool, G (Function.update r i (!(r i))) = ∑ r, G r := by
  simpa using Equiv.sum_comp (Function.Involutive.toPerm _ (flip_involutive i)) G

