/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Finset Filter Asymptotics

/-- The number of points of `𝔽₃ⁿ`, where `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`. -/
lemma card_F3pow (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp

/-- For every `ε > 0` there is an `N` beyond which the constant coming from the corners
theorem is dominated by `3 ^ n`. -/
lemma exists_bound_le_pow (ε : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, cornersTheoremBound ε ≤ 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn => ?_⟩
  calc cornersTheoremBound ε ≤ n := hn
    _ ≤ 3 ^ n := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))

/-- **Cap set theorem** (density form).  For every `ε > 0`, once `n` is large enough, every
3AP-free subset (cap set) of `𝔽₃ⁿ` has size at most `ε · 3ⁿ`. -/
theorem cap_set_density (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  obtain ⟨N, hN⟩ := exists_bound_le_pow ε
  refine ⟨N, fun n hn A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  refine roth_3ap_theorem ε hε ?_ A ?_ hA
  · rw [card_F3pow]; exact hN n hn
  · rw [card_F3pow]; push_cast; exact hlt.le

/-- The size of the largest cap set (3AP-free subset) in `𝔽₃ⁿ`. -/
noncomputable def capSetNumber (n : ℕ) : ℕ :=
  addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))

/-- **The cap set theorem**: subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression
have size `o(3ⁿ)`.

Here `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`, a three-term arithmetic progression is a triple
`a, b, c` with `a + c = b + b` (equivalently `a + b + c = 0` in characteristic three), and
`capSetNumber n` is the largest size of a subset of `𝔽₃ⁿ` containing no non-trivial such triple.

The proof deduces the statement from Roth's theorem for finite abelian groups, `roth_3ap_theorem`,
applied to the group `𝔽₃ⁿ`, whose cardinality `3ⁿ` tends to infinity. -/
theorem cap_set :
    (fun n : ℕ => (capSetNumber n : ℝ)) =o[atTop] fun n : ℕ => (3 : ℝ) ^ n := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set_density ε hε
  rw [eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨A, -, hAcard, hA⟩ :=
    addRothNumber_spec (Finset.univ : Finset (Fin n → ZMod 3))
  have h := hN n hn A hA
  rw [hAcard] at h
  calc ‖(capSetNumber n : ℝ)‖ = (capSetNumber n : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ε * 3 ^ n := h
    _ = ε * ‖(3 : ℝ) ^ n‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end Math2

