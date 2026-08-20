/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

lemma yao_predictor {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) {t : ℕ} (ht : t < m) :
    (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
        (xor (!(p.2 ⟨t, ht⟩)) (D (hyb S f t p.1 p.2))
          == nwGen S f p.1 ⟨t, ht⟩))
      = 1 / 2 + (hybProb S f D (t + 1) - hybProb S f D t) := by
  have key : ∀ x : Fin ℓ → Bool,
      (𝔼 (y : Fin m → Bool), ind ((xor (!(y ⟨t, ht⟩)) (D (hyb S f t x y))) == nwGen S f x ⟨t, ht⟩))
        = 1 / 2 + ((𝔼 (y : Fin m → Bool), ind (D (hyb S f (t + 1) x y)))
            - 𝔼 (y : Fin m → Bool), ind (D (hyb S f t x y))) := by
    intro x
    obtain ⟨b, hb⟩ : ∃ b, nwGen S f x ⟨t, ht⟩ = b := ⟨_, rfl⟩
    have hsucc : ∀ y : Fin m → Bool,
        hyb S f (t + 1) x y = hyb S f t x (Function.update y ⟨t, ht⟩ b) := by
      intro y; rw [hyb_succ S f ht x y, hb]
    simp only [hsucc, hb]
    rw [expect_update_bool ⟨t, ht⟩
        (fun y => ind ((xor (!(y ⟨t, ht⟩)) (D (hyb S f t x y))) == b)),
      expect_update_bool ⟨t, ht⟩ fun y => ind (D (hyb S f t x y))]
    rw [show (1 : ℝ) / 2 = 𝔼 (_y : Fin m → Bool), (1 : ℝ) / 2 from
      (Finset.expect_const univ_nonempty _).symm]
    rw [← Finset.expect_sub_distrib, ← Finset.expect_add_distrib]
    refine Finset.expect_congr rfl fun y _ => ?_
    simp only [Function.update_self]
    cases b <;>
      cases hdt : D (hyb S f t x (Function.update y ⟨t, ht⟩ true)) <;>
      cases hdf : D (hyb S f t x (Function.update y ⟨t, ht⟩ false)) <;>
      norm_num [ind, hdt, hdf]
  rw [pr_prod, hybProb, hybProb, pr_prod, pr_prod]
  simp only []
  rw [Finset.expect_congr rfl fun x _ => key x]
  rw [Finset.expect_add_distrib, Finset.expect_const univ_nonempty, Finset.expect_sub_distrib]

