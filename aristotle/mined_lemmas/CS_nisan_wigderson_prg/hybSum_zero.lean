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

lemma hybSum_zero : hybSum G D 0 = 2 ^ ℓ * ∑ y : Fin m → Bool, ind (D y) := by
  unfold hybSum
  have h0 : ∀ (x : Fin ℓ → Bool) (r : Fin m → Bool), hybridStr G 0 x r = r := by
    intro x r; funext j; simp [hybridStr]
  simp [h0, Finset.card_univ]

