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

noncomputable def predProb (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)
    (i : Fin m) (r : Fin m → Bool) (c : Bool) : ℝ :=
  (∑ x : Fin ℓ → Bool, ind (nwPredictor G D i r c x == G i x)) / 2 ^ ℓ

section Aux

