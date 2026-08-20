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

lemma capSetNumber_le_of_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : cornersTheoremBound ε ≤ 3 ^ n) : (capSetNumber n : ℝ) ≤ ε * 3 ^ n := by
  by_contra h
  push_neg at h
  obtain ⟨A, -, hAcard, hA⟩ :=
    addRothNumber_spec (s := (Finset.univ : Finset (Fin n → ZMod 3)))
  refine roth_3ap_theorem ε hε (by rwa [card_space]) A ?_ hA
  rw [card_space]
  rw [capSetNumber] at h
  rw [hAcard]
  exact_mod_cast h.le

/-- The **cap set theorem**: a subset of `𝔽₃ⁿ` with no non-trivial three-term arithmetic
progression has size at most `ε * 3 ^ n` once `n` is large enough (depending on `ε`). -/
