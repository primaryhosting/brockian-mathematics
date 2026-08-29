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

lemma ov_apply {l n : ℕ} {s : Fin l → Fin n} (hs : Function.Injective s) (x : Fin n → Bool)
    (y : Fin l → Bool) (v : Fin l) : ov s x y (s v) = y v := by
  have h : ∃ w, s w = s v := ⟨v, rfl⟩
  simp only [ov, dif_pos h]
  congr 1
  exact hs h.choose_spec

