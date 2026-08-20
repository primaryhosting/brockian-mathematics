import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- The modular exponentiation function `k ↦ a ^ k mod n`, the function whose period
Shor's algorithm computes. -/

lemma isOfFinOrder_coprime {n a : ℕ} (hn : 0 < n) (h : Nat.Coprime a n) :
    IsOfFinOrder (a : ZMod n) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨Nat.totient n, Nat.totient_pos.mpr hn, ?_⟩
  have h1 : ((a ^ Nat.totient n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient h)
  simpa using h1

/-- The order of `a` in `ZMod n` is a period of `k ↦ a ^ k`. -/
