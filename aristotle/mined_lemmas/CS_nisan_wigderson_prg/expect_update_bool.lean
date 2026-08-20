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

lemma expect_update_bool {m : ℕ} (it : Fin m) (H : (Fin m → Bool) → ℝ) :
    (𝔼 (y : Fin m → Bool), H y)
      = 𝔼 (y : Fin m → Bool), (H (Function.update y it true) + H (Function.update y it false)) / 2 := by
  have hinv : Function.Involutive (fun y : Fin m → Bool => Function.update y it (!(y it))) := by
    intro y
    funext i
    by_cases h : i = it <;> simp [Function.update, h]
  set e : Equiv.Perm (Fin m → Bool) := hinv.toPerm _ with he
  have h1 : (𝔼 (y : Fin m → Bool), H (e y)) = 𝔼 (y : Fin m → Bool), H y :=
    Finset.expect_equiv e (by simp) (fun y _ => rfl)
  have h2 : ∀ y : Fin m → Bool,
      (H (Function.update y it true) + H (Function.update y it false)) / 2
        = (H y + H (e y)) / 2 := by
    intro y
    have hy : Function.update y it (y it) = y := by simp
    cases hyt : y it
    · have h3 : e y = Function.update y it true := by
        simp [he, Function.Involutive.toPerm, hyt]
      rw [h3, show Function.update y it false = y by rw [← hyt]; exact hy]
      ring
    · have h3 : e y = Function.update y it false := by
        simp [he, Function.Involutive.toPerm, hyt]
      rw [h3, show Function.update y it true = y by rw [← hyt]; exact hy]
  rw [Finset.expect_congr rfl (fun y _ => h2 y)]
  have h4 : (𝔼 (y : Fin m → Bool), (H y + H (e y)) / 2)
      = ((𝔼 (y : Fin m → Bool), H y) + 𝔼 (y : Fin m → Bool), H (e y)) / 2 := by
    rw [← Finset.expect_add_distrib, ← Finset.expect_div]
  rw [h4, h1]
  ring

