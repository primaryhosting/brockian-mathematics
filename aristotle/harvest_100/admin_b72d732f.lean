/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] [Inhabited α]

/-- `Sorted a` says that the array `a` is weakly increasing: no later entry is
strictly smaller than an earlier one. -/
def Sorted (a : Array α) : Prop :=
  ∀ i j : Nat, i ≤ j → j < a.size → ¬ (a[j]! < a[i]!)

/-- `IsLinear α` records the trichotomy property of a linear order: two
elements that are incomparable under `<` are equal.  (Every `LinearOrder`
satisfies it; see `isLinear_nat` below for the concrete case of `Nat`.) -/
def IsLinear (α : Type u) [LT α] : Prop :=
  ∀ x y : α, ¬ (x < y) → ¬ (y < x) → x = y

/-- Binary search for the key `k` in the slice `[lo, hi)` of the array `a`.
Returns `some i` for an index `i` holding `k`, and `none` when `k` does not
occur in that slice. -/
def bsearch (a : Array α) (k : α) (lo hi : Nat) : Option Nat :=
  if lo < hi then
    if a[(lo + hi) / 2]! < k then
      bsearch a k ((lo + hi) / 2 + 1) hi
    else if k < a[(lo + hi) / 2]! then
      bsearch a k lo ((lo + hi) / 2)
    else
      some ((lo + hi) / 2)
  else
    none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search over the whole array. -/
def binarySearch (a : Array α) (k : α) : Option Nat := bsearch a k 0 a.size

/-- Soundness (auxiliary form, with an explicit fuel bound on `hi - lo`):
any index returned by binary search lies in the searched slice and really
holds the key. -/
theorem bsearch_sound_aux (a : Array α) (k : α) (hlin : IsLinear α) :
    ∀ n lo hi i : Nat, hi - lo ≤ n → bsearch a k lo hi = some i →
      lo ≤ i ∧ i < hi ∧ a[i]! = k := by
  intro n
  induction n with
  | zero =>
    intro lo hi i hn hres
    rw [bsearch] at hres
    have hle : ¬ (lo < hi) := by omega
    simp only [hle, if_false] at hres
    exact absurd hres (by simp)
  | succ n ih =>
    intro lo hi i hn hres
    rw [bsearch] at hres
    by_cases hlt : lo < hi
    · have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 < hi := by omega
      simp only [hlt, if_true] at hres
      by_cases h1 : a[(lo + hi) / 2]! < k
      · simp only [h1, if_true] at hres
        have := ih ((lo + hi) / 2 + 1) hi i (by omega) hres
        exact ⟨by omega, this.2.1, this.2.2⟩
      · simp only [h1, if_false] at hres
        by_cases h2 : k < a[(lo + hi) / 2]!
        · simp only [h2, if_true] at hres
          have := ih lo ((lo + hi) / 2) i (by omega) hres
          exact ⟨this.1, by omega, this.2.2⟩
        · simp only [h2, if_false, Option.some.injEq] at hres
          subst hres
          exact ⟨hm1, hm2, hlin _ _ h1 h2⟩
    · simp only [hlt, if_false] at hres
      exact absurd hres (by simp)

/-- Soundness: any index returned by binary search lies in the searched slice
and really holds the key.  (No sortedness assumption is needed here.) -/
theorem bsearch_sound (a : Array α) (k : α) (hlin : IsLinear α)
    (lo hi i : Nat) (hres : bsearch a k lo hi = some i) :
    lo ≤ i ∧ i < hi ∧ a[i]! = k :=
  bsearch_sound_aux a k hlin (hi - lo) lo hi i (Nat.le_refl _) hres

/-- Correctness on a slice (auxiliary form, with an explicit fuel bound):
binary search on `[lo, hi)` succeeds iff the key occurs in that slice. -/
theorem bsearch_isSome_iff_aux (a : Array α) (k : α)
    (hlin : IsLinear α) (hsort : Sorted a) :
    ∀ n lo hi : Nat, hi - lo ≤ n → hi ≤ a.size →
      ((bsearch a k lo hi).isSome ↔ ∃ i : Nat, lo ≤ i ∧ i < hi ∧ a[i]! = k) := by
  intro n
  induction n with
  | zero =>
    intro lo hi hn hhi
    have hle : ¬ (lo < hi) := by omega
    rw [bsearch]
    simp only [hle, if_false, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨i, h1, h2, -⟩
    omega
  | succ n ih =>
    intro lo hi hn hhi
    rw [bsearch]
    by_cases hlt : lo < hi
    · have hm1 : lo ≤ (lo + hi) / 2 := by omega
      have hm2 : (lo + hi) / 2 < hi := by omega
      simp only [hlt, if_true]
      by_cases h1 : a[(lo + hi) / 2]! < k
      · simp only [h1, if_true]
        rw [ih ((lo + hi) / 2 + 1) hi (by omega) hhi]
        constructor
        · rintro ⟨i, hi1, hi2, hi3⟩
          exact ⟨i, by omega, hi2, hi3⟩
        · rintro ⟨i, hi1, hi2, hi3⟩
          refine ⟨i, ?_, hi2, hi3⟩
          rcases Nat.lt_or_ge ((lo + hi) / 2) i with h | h
          · omega
          · have hcon := hsort i ((lo + hi) / 2) h (by omega)
            rw [hi3] at hcon
            exact absurd h1 hcon
      · simp only [h1, if_false]
        by_cases h2 : k < a[(lo + hi) / 2]!
        · simp only [h2, if_true]
          rw [ih lo ((lo + hi) / 2) (by omega) (by omega)]
          constructor
          · rintro ⟨i, hi1, hi2, hi3⟩
            exact ⟨i, hi1, by omega, hi3⟩
          · rintro ⟨i, hi1, hi2, hi3⟩
            refine ⟨i, hi1, ?_, hi3⟩
            rcases Nat.lt_or_ge i ((lo + hi) / 2) with h | h
            · exact h
            · have hcon := hsort ((lo + hi) / 2) i h (by omega)
              rw [hi3] at hcon
              exact absurd h2 hcon
        · simp only [h2, if_false]
          have heq : a[(lo + hi) / 2]! = k := hlin _ _ h1 h2
          simp only [Option.isSome_some, true_iff]
          exact ⟨(lo + hi) / 2, hm1, hm2, heq⟩
    · simp only [hlt, if_false, Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨i, ha, hb, -⟩
      omega

/-- Correctness on a slice: on a sorted array, binary search on `[lo, hi)`
succeeds iff the key occurs in that slice. -/
theorem bsearch_isSome_iff (a : Array α) (k : α)
    (hlin : IsLinear α) (hsort : Sorted a) (lo hi : Nat) (hhi : hi ≤ a.size) :
    (bsearch a k lo hi).isSome ↔ ∃ i : Nat, lo ≤ i ∧ i < hi ∧ a[i]! = k :=
  bsearch_isSome_iff_aux a k hlin hsort (hi - lo) lo hi (Nat.le_refl _) hhi

/-- **Binary search is correct**: on a sorted array, binary search returns an
index if and only if the key is present in the array. -/
theorem binary_search_correct (a : Array α) (k : α)
    (hlin : IsLinear α) (hsort : Sorted a) :
    (binarySearch a k).isSome ↔ ∃ i : Nat, ∃ h : i < a.size, a[i] = k := by
  rw [binarySearch, bsearch_isSome_iff a k hlin hsort 0 a.size (Nat.le_refl _)]
  constructor
  · rintro ⟨i, -, h2, h3⟩
    refine ⟨i, h2, ?_⟩
    rw [← getElem!_pos a i h2]
    exact h3
  · rintro ⟨i, h, h3⟩
    refine ⟨i, Nat.zero_le _, h, ?_⟩
    rw [getElem!_pos a i h]
    exact h3

/-- Moreover, when binary search succeeds it returns a genuine witness: an
in-range index whose entry is the key. -/
theorem binary_search_returns_index (a : Array α) (k : α) (hlin : IsLinear α)
    (i : Nat) (hres : binarySearch a k = some i) :
    ∃ h : i < a.size, a[i] = k := by
  have h := bsearch_sound a k hlin 0 a.size i hres
  exact ⟨h.2.1, by rw [← getElem!_pos a i h.2.1]; exact h.2.2⟩

/-- `Nat` (with its usual `<`) satisfies the trichotomy hypothesis, so the
correctness theorem applies to arrays of natural numbers. -/
theorem isLinear_nat : IsLinear Nat := by
  intro x y hxy hyx
  omega

/-- Concrete instance of the main theorem for `Array Nat`. -/
theorem binary_search_correct_nat (a : Array Nat) (k : Nat) (hsort : Sorted a) :
    (binarySearch a k).isSome ↔ ∃ i : Nat, ∃ h : i < a.size, a[i] = k :=
  binary_search_correct a k isLinear_nat hsort

end CS

import RequestProject.Main
import Mathlib

/-!
# Binary search correctness for an arbitrary `LinearOrder` (Mathlib version)

The core development in `RequestProject.Main` is stated for a type with a
decidable `<` satisfying trichotomy (`CS.IsLinear`).  Here we specialise it to
Mathlib's `LinearOrder`, where the hypotheses are automatic and sortedness can
be phrased with `≤`.
-/

namespace CS

variable {α : Type*} [LinearOrder α] [Inhabited α]

omit [Inhabited α] in
theorem isLinear_of_linearOrder : IsLinear α := fun _ _ hxy hyx =>
  le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)

theorem sorted_of_monotone {a : Array α}
    (h : ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!) : Sorted a :=
  fun i j hij hj => not_lt.mpr (h i j hij hj)

/-- **Binary search is correct** over an arbitrary linear order: on a sorted
array, binary search returns an index iff the key is present. -/
theorem binary_search_correct_linearOrder (a : Array α) (k : α)
    (hsort : ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    (binarySearch a k).isSome ↔ ∃ i : ℕ, ∃ h : i < a.size, a[i] = k :=
  binary_search_correct a k isLinear_of_linearOrder (sorted_of_monotone hsort)

end CS

