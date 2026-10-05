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

theorem orderOf_eq_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hn : 0 < n)
    (h : x ^ n = 1) (h' : ∀ k, 0 < k → k < n → x ^ k ≠ 1) : orderOf x = n := by
  have hdvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one h
  have hpos : 0 < orderOf x := by
    rcases Nat.eq_zero_or_pos (orderOf x) with h0 | h0
    · rw [h0] at hdvd
      omega
    · exact h0
  have hle : orderOf x ≤ n := Nat.le_of_dvd hn hdvd
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  · exact absurd (pow_orderOf_eq_one x) (h' _ hpos hlt)

/-- A concrete base case: `2` is a primitive root modulo `5`. -/
