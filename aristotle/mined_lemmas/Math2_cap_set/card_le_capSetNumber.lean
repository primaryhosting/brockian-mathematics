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

lemma card_le_capSetNumber {n : ℕ} (A : Finset (Fin n → ZMod 3))
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) : #A ≤ capSetNumber n :=
  ThreeAPFree.le_addRothNumber hA (Finset.subset_univ _)

/-- Quantitative form of the cap set bound, coming from Roth's theorem for finite abelian
groups: if `3 ^ n` is large enough in terms of `ε`, then every 3AP-free subset of `𝔽₃ⁿ`
has size at most `ε * 3 ^ n`. -/
