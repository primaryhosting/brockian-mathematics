import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Filter Finset

/-- The *cap set number* `capSetNumber n` is the largest size of a subset of `𝔽₃ⁿ`
containing no non-trivial three-term arithmetic progression (a *cap set*).

Here `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`, and `ThreeAPFree` is Mathlib's predicate saying
that `a + c = b + b` with `a, b, c` in the set forces `a = b` (hence `a = b = c`). -/

theorem cap_set_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn A hA ↦ ?_⟩
  have hpow : cornersTheoremBound ε ≤ 3 ^ n :=
    hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  refine le_trans ?_ (capSetNumber_le_of_le hε hpow)
  exact_mod_cast card_le_capSetNumber A hA

/-- The **cap set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt, here obtained from Roth's
