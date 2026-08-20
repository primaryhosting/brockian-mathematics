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

lemma exists_predictor {n m ℓ d : ℕ} {S : Fin m → Fin n → Fin ℓ}
    (hSinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      (univ.filter fun k : Fin n => ∃ k', S j k' = S i k).card ≤ d)
    (f : (Fin n → Bool) → Bool) (D : (Fin m → Bool) → Bool) {t : ℕ} (ht : t < m) :
    ∃ g : (Fin n → Bool) → Bool, IsNWPredictor d D t g ∧
      1 / 2 + |hybProb S f D (t + 1) - hybProb S f D t| ≤ pr fun z => g z == f z := by
  have hyao := yao_predictor S f D ht
  rcases le_or_gt 0 (hybProb S f D (t + 1) - hybProb S f D t) with hδ | hδ
  · obtain ⟨g, hg, hle⟩ :=
      glue_predictor hSinj hdesign f D ht fun y : Fin m → Bool => !(y ⟨t, ht⟩)
    refine ⟨g, hg, ?_⟩
    rw [abs_of_nonneg hδ, ← hyao]
    exact hle
  · obtain ⟨g, hg, hle⟩ :=
      glue_predictor hSinj hdesign f D ht fun y : Fin m → Bool => y ⟨t, ht⟩
    refine ⟨g, hg, ?_⟩
    have hrw : (pr fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
          (xor (p.2 ⟨t, ht⟩) (D (hyb S f t p.1 p.2)) == nwGen S f p.1 ⟨t, ht⟩))
        = 1 - (1 / 2 + (hybProb S f D (t + 1) - hybProb S f D t)) := by
      rw [← hyao, ← pr_not (fun p : (Fin ℓ → Bool) × (Fin m → Bool) =>
        xor (!(p.2 ⟨t, ht⟩)) (D (hyb S f t p.1 p.2))) fun p => nwGen S f p.1 ⟨t, ht⟩]
      congr 1
      funext p
      have hxor : ∀ a w : Bool, xor a w = !(xor (!a) w) := by decide
      rw [hxor]
    rw [abs_of_neg hδ]
    calc 1 / 2 + -(hybProb S f D (t + 1) - hybProb S f D t)
        = 1 - (1 / 2 + (hybProb S f D (t + 1) - hybProb S f D t)) := by ring
      _ = _ := hrw.symm
      _ ≤ _ := hle

