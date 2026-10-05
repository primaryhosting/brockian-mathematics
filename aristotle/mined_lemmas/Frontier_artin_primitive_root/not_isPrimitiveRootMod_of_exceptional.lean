import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single import.)

namespace Frontier

/-! ## Definitions -/

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

theorem not_isPrimitiveRootMod_of_exceptional
    (a : ℤ) (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (ha : a = -1 ∨ IsSquare a) :
    ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  intro hord
  rw [IsPrimitiveRootMod] at hord
  rcases ha with rfl | ⟨b, rfl⟩
  · -- `-1` has order at most `2`, so it can only be a primitive root when `p - 1 ≤ 2`.
    have h2 : (((-1 : ℤ)) : ZMod p) ^ 2 = 1 := by push_cast; ring
    have hle : orderOf (((-1 : ℤ)) : ZMod p) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · by_cases hb : ((b : ℤ) : ZMod p) = 0
    · -- a square of a multiple of `p` is `0`, which has no finite order.
      have hz : (((b * b : ℤ)) : ZMod p) = 0 := by push_cast at hb ⊢; rw [hb]; ring
      have h1 : (((b * b : ℤ)) : ZMod p) ^ orderOf (((b * b : ℤ)) : ZMod p) = 1 :=
        pow_orderOf_eq_one _
      rw [hz] at h1 hord
      rw [hord, zero_pow (by omega)] at h1
      exact zero_ne_one h1
    · -- a nonzero square has order dividing `(p - 1) / 2`, by Fermat's little theorem.
      set m := (p - 1) / 2 with hm
      have hpm : 2 * m = p - 1 := by omega
      have hpow : (((b * b : ℤ)) : ZMod p) ^ m = 1 := by
        have hrw : (((b * b : ℤ)) : ZMod p) ^ m = ((b : ℤ) : ZMod p) ^ (2 * m) := by
          push_cast; ring
        rw [hrw, hpm]
        exact ZMod.pow_card_sub_one_eq_one hb
      have hle : orderOf (((b * b : ℤ)) : ZMod p) ≤ m :=
        Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)
      omega

/-- **Lean-checked reduction for Artin's conjecture.**
The excluded cases in Artin's conjecture are genuinely exceptional: if `a = -1` or `a` is a
perfect square, then `a` is a primitive root modulo only finitely many primes (in fact only
possibly `p = 2` or `p = 3`).  Equivalently, the hypotheses `a ≠ -1` and `¬ IsSquare a` in
`Frontier.ArtinConjecture` cannot be dropped. -/
