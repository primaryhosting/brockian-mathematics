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

lemma ov_ov {l n : ℕ} {s : Fin l → Fin n} (hs : Function.Injective s) (x : Fin n → Bool)
    (y : Fin l → Bool) : ov s (ov s x y) (fun v => x (s v)) = x := by
  funext t
  by_cases h : ∃ v, s v = t
  · obtain ⟨v, rfl⟩ := h
    exact ov_apply hs _ _ v
  · simp only [ov, dif_neg h]

/-- Averaging over the overwritten string is the same as averaging over the original one. -/
