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

lemma sum_ov {l n : ℕ} {s : Fin l → Fin n} (hs : Function.Injective s) (F : (Fin n → Bool) → ℝ) :
    ∑ x : Fin n → Bool, ∑ y : Fin l → Bool, F (ov s x y)
      = 2 ^ l * ∑ x : Fin n → Bool, F x := by
  have hinv : Function.Involutive
      (fun p : (Fin n → Bool) × (Fin l → Bool) => (ov s p.1 p.2, fun v => p.1 (s v))) := by
    rintro ⟨x, y⟩
    have h1 : ov s (ov s x y) (fun v => x (s v)) = x := ov_ov hs x y
    have h2 : (fun v => (ov s x y) (s v)) = y := funext (ov_apply hs x y)
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  have key := Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
    (fun p : (Fin n → Bool) × (Fin l → Bool) => F p.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at key
  simpa [Finset.mul_sum] using key

