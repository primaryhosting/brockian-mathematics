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

open Finset Asymptotics Filter

/-- The cap set number `capSetNumber n` is the largest cardinality of a subset of
`𝔽₃ⁿ = (Fin n → ZMod 3)` containing no nontrivial three-term arithmetic progression. -/
noncomputable def capSetNumber (n : ℕ) : ℕ :=
  addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))

/-- A cap set of `𝔽₃ⁿ` of maximal size exists: it is 3AP-free and has `capSetNumber n` elements. -/
lemma exists_capSet (n : ℕ) :
    ∃ A : Finset (Fin n → ZMod 3), #A = capSetNumber n ∧
      ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  obtain ⟨A, -, hcard, hAP⟩ := addRothNumber_spec (Finset.univ : Finset (Fin n → ZMod 3))
  exact ⟨A, hcard, hAP⟩

/-- The number of points of `𝔽₃ⁿ`. -/
lemma card_F3 (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp

/-- Quantitative form of the cap set theorem: for every `ε > 0` there is `N` such that for all
`n ≥ N`, every 3AP-free subset of `𝔽₃ⁿ` has fewer than `ε * 3ⁿ` elements. -/
theorem cap_set_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset (Fin n → ZMod 3),
      ThreeAPFree (A : Set (Fin n → ZMod 3)) → (#A : ℝ) < ε * 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn A hA => ?_⟩
  by_contra hcon
  push_neg at hcon
  refine roth_3ap_theorem (G := Fin n → ZMod 3) ε hε ?_ A ?_ hA
  · have h1 : cornersTheoremBound ε < 3 ^ cornersTheoremBound ε :=
      Nat.lt_pow_self (by norm_num)
    have h2 : (3 : ℕ) ^ cornersTheoremBound ε ≤ 3 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hn
    rw [card_F3]
    exact le_trans h1.le h2
  · rw [card_F3]
    push_cast
    exact hcon

/-- **The cap set theorem**: subsets of `𝔽₃ⁿ` with no nontrivial three-term arithmetic
progression have size `o(3ⁿ)`. -/
theorem cap_set :
    IsLittleO atTop (fun n : ℕ => (capSetNumber n : ℝ)) (fun n : ℕ => (3 : ℝ) ^ n) := by
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set_eps ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨A, hcard, hAP⟩ := exists_capSet n
  have h := hN n hn A hAP
  rw [hcard] at h
  have h3 : ‖(3 : ℝ) ^ n‖ = 3 ^ n := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Real.norm_natCast, h3]
  exact h.le

end Math2

