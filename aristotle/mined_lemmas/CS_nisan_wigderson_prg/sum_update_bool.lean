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

lemma sum_update_bool (i : Fin m) (F : (Fin m → Bool) → ℝ) :
    ∑ b : Bool, ∑ r : Fin m → Bool, F (Function.update r i b) = 2 * ∑ r : Fin m → Bool, F r := by
  have hinv : Function.Involutive (fun r : Fin m → Bool => Function.update r i (!(r i))) := by
    intro r
    simp [Function.update_idem]
  have hswap : ∑ r : Fin m → Bool, F (Function.update r i (!(r i)))
      = ∑ r : Fin m → Bool, F r :=
    Equiv.sum_comp (hinv.toPerm _) F
  rw [Finset.sum_comm]
  have hpt : ∀ r : Fin m → Bool, ∑ b : Bool, F (Function.update r i b)
      = F r + F (Function.update r i (!(r i))) := by
    intro r
    rw [Fintype.sum_bool]
    cases h : r i
    · rw [show Function.update r i false = r by rw [← h]; exact Function.update_eq_self i r]
      simp only [Bool.not_false]
      ring
    · rw [show Function.update r i true = r by rw [← h]; exact Function.update_eq_self i r]
      simp only [Bool.not_true]
  calc ∑ r : Fin m → Bool, ∑ b : Bool, F (Function.update r i b)
      = ∑ r : Fin m → Bool, (F r + F (Function.update r i (!(r i)))) := by
        exact Finset.sum_congr rfl fun r _ => hpt r
    _ = (∑ r : Fin m → Bool, F r) + ∑ r : Fin m → Bool, F (Function.update r i (!(r i))) :=
        Finset.sum_add_distrib
    _ = 2 * ∑ r : Fin m → Bool, F r := by rw [hswap]; ring

/-- The `(i+1)`-st hybrid is the `i`-th hybrid with the `i`-th random bit overwritten by
the generator bit. -/
