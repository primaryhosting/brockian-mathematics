import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open Fintype (card)

namespace Math2

variable {n : ℕ}

/-- A *cap set* in `𝔽₃ⁿ`: a set containing no three (not necessarily distinct) points on a line,
i.e. whenever `x + y + z = 0` for `x, y, z` in the set, the three points coincide.

Since `3 • v = 0` in `𝔽₃ⁿ`, the condition `x + y + z = 0` says exactly that `x, y, z` form a
three-term arithmetic progression, so this is equivalent to `ThreeAPFree`. -/
def IsCapSet (A : Set (Fin n → ZMod 3)) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A → x + y + z = 0 → x = y ∧ y = z

private lemma three_nsmul_eq_zero (x : Fin n → ZMod 3) : x + x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  revert i
  intro i
  generalize x i = a
  revert a
  decide

/-- Being a cap set is the same as being free of three-term arithmetic progressions. -/
theorem isCapSet_iff_threeAPFree (A : Set (Fin n → ZMod 3)) :
    IsCapSet A ↔ ThreeAPFree A := by
  constructor
  · intro hA a ha b hb c hc habc
    have h : a + b + c = 0 := by
      have h3 := three_nsmul_eq_zero b
      have : a + c = b + b := habc
      linear_combination (norm := abel_nf) this + h3 - (b + b + b) + (b + b + b)
    exact ((hA ha hb hc h).1.trans (hA ha hb hc h).2)
  · intro hA x hx y hy z hz hxyz
    have hxy : x = y := by
      refine hA hx hz hy ?_
      have h3 := three_nsmul_eq_zero z
      linear_combination (norm := abel_nf) hxyz + h3 - (z + z + z) + (z + z + z)
    have hyz : y = z := by
      refine hA hy hx hz ?_
      have h3 := three_nsmul_eq_zero x
      linear_combination (norm := abel_nf) hxyz + h3 - (x + x + x) + (x + x + x)
    exact ⟨hxy, hyz⟩

open Classical in
/-- The largest possible size of a cap set in `𝔽₃ⁿ`. -/
noncomputable def capSetNumber (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → ZMod 3))).filter
    fun A => ThreeAPFree (A : Set (Fin n → ZMod 3))).sup Finset.card

/-- Every cap set in `𝔽₃ⁿ` has size at most `capSetNumber n`. -/
theorem card_le_capSetNumber (A : Finset (Fin n → ZMod 3))
    (hA : IsCapSet (A : Set (Fin n → ZMod 3))) : #A ≤ capSetNumber n := by
  classical
  refine Finset.le_sup (f := Finset.card) ?_
  simpa [(isCapSet_iff_threeAPFree _).1 hA] using
    Finset.mem_filter.2 ⟨Finset.mem_univ A, (isCapSet_iff_threeAPFree _).1 hA⟩

/-- The bound `capSetNumber n` is attained by an actual cap set. -/
theorem exists_capSet_card_eq (n : ℕ) :
    ∃ A : Finset (Fin n → ZMod 3), IsCapSet (A : Set (Fin n → ZMod 3)) ∧
      #A = capSetNumber n := by
  classical
  have hne : (((Finset.univ : Finset (Finset (Fin n → ZMod 3))).filter
      fun A => ThreeAPFree (A : Set (Fin n → ZMod 3)))).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [threeAPFree_empty]⟩⟩
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨A, ?_, ?_⟩
  · exact (isCapSet_iff_threeAPFree _).2 (Finset.mem_filter.1 hA).2
  · rw [capSetNumber, ← hAcard]

private lemma card_space (n : ℕ) : card (Fin n → ZMod 3) = 3 ^ n := by
  simp

/-- Quantitative form: for every `ε > 0`, all sufficiently large `n` are such that every cap set
in `𝔽₃ⁿ` has size at most `ε * 3 ^ n`. -/
theorem capSetNumber_le_of_le (ε : ℝ) (hε : 0 < ε) {n : ℕ} (hn : cornersTheoremBound ε ≤ n) :
    (capSetNumber n : ℝ) ≤ ε * 3 ^ n := by
  classical
  obtain ⟨A, hA, hAcard⟩ := exists_capSet_card_eq n
  have hcard : cornersTheoremBound ε ≤ card (Fin n → ZMod 3) := by
    rw [card_space]
    exact hn.trans (Nat.lt_pow_self (by norm_num)).le
  have := roth_3ap_theorem ε hε hcard A
  rw [← hAcard]
  by_contra h
  push_neg at h
  refine this ?_ ((isCapSet_iff_threeAPFree _).1 hA)
  rw [card_space]
  push_cast
  exact h.le

/-- **The cap set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt, here obtained from Roth's
theorem for finite abelian groups): subsets of `𝔽₃ⁿ` with no three-term arithmetic progression
have size `o(3ⁿ)`. -/
theorem cap_set :
    IsLittleO atTop (fun n : ℕ => (capSetNumber n : ℝ)) (fun n : ℕ => (3 : ℝ) ^ n) := by
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (cornersTheoremBound ε)] with n hn
  have h := capSetNumber_le_of_le ε hε hn
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ n)]
  exact h

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

