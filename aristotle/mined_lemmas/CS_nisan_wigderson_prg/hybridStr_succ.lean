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

lemma hybridStr_succ (G : Fin m → (Fin ℓ → Bool) → Bool) (i : Fin m)
    (x : Fin ℓ → Bool) (r : Fin m → Bool) :
    hybridStr G ((i : ℕ) + 1) x r = hybridStr G i x (Function.update r i (G i x)) := by
  funext j
  rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
  · have hlt : (j : ℕ) < (i : ℕ) + 1 := by omega
    simp [hybridStr, hlt, h]
  · have hj : j = i := Fin.ext h
    subst hj
    simp [hybridStr]
  · have h1 : ¬ ((j : ℕ) < (i : ℕ) + 1) := by omega
    have h2 : ¬ ((j : ℕ) < (i : ℕ)) := by omega
    have hne : j ≠ i := by
      intro hj; subst hj; omega
    simp [hybridStr, h1, h2, Function.update_of_ne hne]

end Aux

section Core

variable (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)

/-- The unnormalised number of `(x, r)` pairs on which the (uncomplemented) next-bit
predictor for position `i` is correct, expressed through two consecutive hybrids. -/
