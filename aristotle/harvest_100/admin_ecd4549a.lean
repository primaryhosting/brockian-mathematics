/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` lines to precede every command, including module
-- docstrings (`/-! ... -/`), so the header is repeated below as the module docstring.
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Math2

/-- The maximal size of a cap set in `𝔽₃ⁿ`, i.e. of a subset of `(Fin n → ZMod 3)` containing
no three-term arithmetic progression. -/
noncomputable def capSetCard (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = k}

lemma card_space (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp

lemma capSetCard_bddAbove (n : ℕ) :
    BddAbove {k | ∃ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = k} :=
  ⟨3 ^ n, by
    rintro k ⟨A, -, rfl⟩
    simpa [card_space] using A.card_le_univ⟩

lemma capSetCard_nonempty (n : ℕ) :
    {k | ∃ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = k}.Nonempty :=
  ⟨0, ∅, by simp, by simp⟩

/-- Every 3AP-free subset of `𝔽₃ⁿ` has at most `capSetCard n` elements. -/
lemma card_le_capSetCard {n : ℕ} (A : Finset (Fin n → ZMod 3))
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) : #A ≤ capSetCard n :=
  le_csSup (capSetCard_bddAbove n) ⟨A, hA, rfl⟩

/-- `capSetCard n` is bounded by any bound valid for all 3AP-free subsets of `𝔽₃ⁿ`. -/
lemma capSetCard_le {n B : ℕ}
    (h : ∀ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) → #A ≤ B) :
    capSetCard n ≤ B :=
  csSup_le (capSetCard_nonempty n) (by rintro k ⟨A, hA, rfl⟩; exact h A hA)

/-- Quantitative form of the cap set bound: for every `ε > 0`, all sufficiently large `n` are such
that every 3AP-free subset of `𝔽₃ⁿ` has size at most `ε * 3 ^ n`.

This is deduced from Roth's theorem for finite abelian groups (`roth_3ap_theorem` in Mathlib),
applied to the group `𝔽₃ⁿ = (Fin n → ZMod 3)`. -/
theorem cap_set_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) ≤ ε * 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn A hA ↦ ?_⟩
  have hcard : (Fintype.card (Fin n → ZMod 3) : ℝ) = 3 ^ n := by
    rw [card_space]; push_cast; ring
  have hbound : cornersTheoremBound ε ≤ Fintype.card (Fin n → ZMod 3) := by
    rw [card_space]
    exact hn.trans (Nat.le_of_lt (Nat.lt_pow_self (by norm_num)))
  by_contra hlt
  push_neg at hlt
  exact roth_3ap_theorem ε hε hbound A (by rw [hcard]; exact hlt.le) hA

/-- **The cap set theorem**: subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression have
size `o(3ⁿ)`. -/
theorem cap_set : Tendsto (fun n : ℕ ↦ (capSetCard n : ℝ) / 3 ^ n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set_eps (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hpos : (0 : ℝ) < 3 ^ n := by positivity
  have hle : (capSetCard n : ℝ) ≤ ε / 2 * 3 ^ n := by
    obtain ⟨A, hA, hAcard⟩ : ∃ A : Finset (Fin n → ZMod 3),
        ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = capSetCard n :=
      Nat.sSup_mem (capSetCard_nonempty n) (capSetCard_bddAbove n)
    rw [← hAcard]
    exact hN n hn A hA
  have h0 : (0 : ℝ) ≤ (capSetCard n : ℝ) / 3 ^ n := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0, div_lt_iff₀ hpos]
  calc (capSetCard n : ℝ) ≤ ε / 2 * 3 ^ n := hle
    _ < ε * 3 ^ n := by nlinarith

end Math2

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

