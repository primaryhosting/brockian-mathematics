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

lemma corr_true_eq (i : Fin m) :
    ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r true x == G i x)
      = 2 ^ ℓ * 2 ^ m
        - ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r false x == G i x) := by
  have hpt : ∀ (x : Fin ℓ → Bool) (r : Fin m → Bool),
      ind (nwPredictor G D i r true x == G i x)
        = 1 - ind (nwPredictor G D i r false x == G i x) := by
    intro x r
    have hnot : nwPredictor G D i r true x = !(nwPredictor G D i r false x) := by
      simp [nwPredictor]
    rw [hnot, ← ind_not]
    congr 1
    cases nwPredictor G D i r false x <;> cases G i x <;> simp
  calc ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool, ind (nwPredictor G D i r true x == G i x)
      = ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool,
          (1 - ind (nwPredictor G D i r false x == G i x)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => hpt x r
    _ = 2 ^ ℓ * 2 ^ m
        - ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool,
            ind (nwPredictor G D i r false x == G i x) := by
        simp [Finset.sum_sub_distrib, Finset.card_univ, Finset.sum_const]

