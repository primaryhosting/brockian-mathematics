import Mathlib
/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
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

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Auxiliary binary search: searches for `key` in the half-open index range
`[lo, hi)` of the array `a`. -/
def bsearchAux (a : Array α) (key : α) (lo hi : ℕ) : Option ℕ :=
  if h : lo < hi ∧ (lo + hi) / 2 < a.size then
    if a[(lo + hi) / 2]'h.2 < key then
      bsearchAux a key ((lo + hi) / 2 + 1) hi
    else if key < a[(lo + hi) / 2]'h.2 then
      bsearchAux a key lo ((lo + hi) / 2)
    else
      some ((lo + hi) / 2)
  else
    none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search for `key` in the array `a`. -/
def bsearch (a : Array α) (key : α) : Option ℕ :=
  bsearchAux a key 0 a.size

/-- `Sorted a` says the array `a` is sorted in non-decreasing order. -/
def Sorted (a : Array α) : Prop :=
  ∀ i j, ∀ (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]

/-- **Soundness**: whenever `bsearchAux` returns an index, that index is in range
and the array holds `key` there. -/
theorem bsearchAux_sound (a : Array α) (key : α) :
    ∀ n lo hi k, hi - lo ≤ n → bsearchAux a key lo hi = some k →
      ∃ h : k < a.size, a[k] = key := by
  intro n
  induction n with
  | zero =>
    intro lo hi k hn hk
    rw [bsearchAux, dif_neg (by omega)] at hk
    exact absurd hk (by simp)
  | succ n ih =>
    intro lo hi k hn hk
    rw [bsearchAux] at hk
    split at hk
    · rename_i h
      split at hk
      · exact ih _ _ k (by omega) hk
      · split at hk
        · exact ih _ _ k (by omega) hk
        · rename_i h1 h2
          have hkm : k = (lo + hi) / 2 := by simpa using hk.symm
          subst hkm
          exact ⟨h.2, le_antisymm (not_lt.mp h2) (not_lt.mp h1)⟩
    · exact absurd hk (by simp)

/-- **Completeness**: if a sorted array contains `key` at an index inside the
search window `[lo, hi)`, then `bsearchAux` succeeds. -/
theorem bsearchAux_complete (a : Array α) (key : α) (hs : Sorted a) :
    ∀ n lo hi i, ∀ (hia : i < a.size), hi - lo ≤ n → hi ≤ a.size → lo ≤ i → i < hi →
      a[i] = key → (bsearchAux a key lo hi).isSome := by
  intro n
  induction n with
  | zero =>
    intro lo hi i hia hn hha hli hih hai
    omega
  | succ n ih =>
    intro lo hi i hia hn hha hli hih hai
    have hmidlt : (lo + hi) / 2 < a.size := by omega
    rw [bsearchAux, dif_pos (⟨by omega, hmidlt⟩ : lo < hi ∧ (lo + hi) / 2 < a.size)]
    by_cases h1 : a[(lo + hi) / 2]'hmidlt < key
    · rw [if_pos h1]
      have himid : (lo + hi) / 2 < i := by
        by_contra hcon
        push_neg at hcon
        have hle := hs i ((lo + hi) / 2) hia hmidlt hcon
        rw [hai] at hle
        exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)
      exact ih _ _ i hia (by omega) hha (by omega) hih hai
    · rw [if_neg h1]
      by_cases h2 : key < a[(lo + hi) / 2]'hmidlt
      · rw [if_pos h2]
        have himid : i < (lo + hi) / 2 := by
          by_contra hcon
          push_neg at hcon
          have hle := hs ((lo + hi) / 2) i hmidlt hia hcon
          rw [hai] at hle
          exact absurd (lt_of_lt_of_le h2 hle) (lt_irrefl _)
        exact ih _ _ i hia (by omega) (by omega) hli himid hai
      · rw [if_neg h2]
        simp

/-- **Binary search is correct.**  For a sorted array `a`, `bsearch a key`
returns some index exactly when `key` occurs in `a`; moreover any index it
returns is a valid position at which `key` occurs. -/
theorem binary_search_correct (a : Array α) (key : α) (hs : Sorted a) :
    (∀ k, bsearch a key = some k → ∃ h : k < a.size, a[k] = key) ∧
      ((bsearch a key).isSome ↔ ∃ i, ∃ h : i < a.size, a[i] = key) := by
  refine ⟨fun k hk => bsearchAux_sound a key a.size 0 a.size k (by omega) hk, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hk1, hk2⟩ := bsearchAux_sound a key a.size 0 a.size k (by omega) hk
    exact ⟨k, hk1, hk2⟩
  · rintro ⟨i, hi, hai⟩
    exact bsearchAux_complete a key hs a.size 0 a.size i hi (by omega) le_rfl
      (Nat.zero_le _) hi hai

end CS

