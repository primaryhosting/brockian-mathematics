import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma exists_small_determining_set {n : ℕ} (s : V n) (hs : s ≠ 0) :
    ∃ Y : Finset (V n), Y.card ≤ n ∧ ∀ v : V n, (∀ y ∈ Y, dotp y v = 0) ↔ (v = 0 ∨ v = s) := by
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, s i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hs (funext hcon)
  have hi0' : s i0 = 1 := zmod2_eq_one_of_ne_zero hi0
  set yv : Fin n → V n :=
    fun j i => (if i = j then (1 : ZMod 2) else 0) + (if i = i0 then s j else 0) with hyv
  have key : ∀ (j : Fin n) (v : V n), dotp (yv j) v = v j + s j * v i0 := by
    intro j v
    simp [dotp, hyv, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']
  refine ⟨(Finset.univ.erase i0).image yv, ?_, ?_⟩
  · refine le_trans (Finset.card_image_le) ?_
    simp
  · intro v
    constructor
    · intro h
      have hall : ∀ j : Fin n, v j = s j * v i0 := by
        intro j
        by_cases hji : j = i0
        · subst hji; simp [hi0']
        · have hmem : yv j ∈ (Finset.univ.erase i0).image yv :=
            Finset.mem_image_of_mem yv (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
          have := h (yv j) hmem
          rw [key j v] at this
          exact zmod2_eq_of_add_eq_zero this
      rcases zmod2_cases (v i0) with h0 | h1
      · left
        funext j
        rw [hall j, h0, mul_zero]
        rfl
      · right
        funext j
        rw [hall j, h1, mul_one]
    · intro hv y hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      rw [key j v]
      rcases hv with h0 | h0 <;> subst h0
      · simp
      · simp [hi0', zmod2_add_self]

/-! ## The classical side: deterministic query algorithms -/

/-- A deterministic classical query algorithm of depth at most `d`: a decision tree whose
internal nodes query the oracle at a point of `(ℤ/2)ⁿ` and branch on the answer, and whose
leaves output a Boolean verdict. -/
inductive DTree (n : ℕ) : ℕ → Type where
  | leaf : ∀ {d : ℕ}, Bool → DTree n d
  | query : ∀ {d : ℕ}, V n → (V n → DTree n d) → DTree n (d + 1)

/-- The verdict of the algorithm on the oracle `f`. -/
