import Mathlib
import RequestProject.Main

/-!
# Binary search correctness, stated with Mathlib's `LinearOrder`

`CS.binary_search_correct` in `RequestProject/Main.lean` is stated using the Lean core
order classes `Std.IsLinearOrder` / `Std.LawfulOrderLT`. Mathlib's `LinearOrder`
provides both, so the statement specializes immediately, as recorded here.
-/

set_option autoImplicit false

namespace CS

universe u

/-- Binary search on a sorted array over a Mathlib `LinearOrder` returns an index
if and only if the key occurs in the array. -/
theorem binary_search_correct_linearOrder {α : Type u} [LinearOrder α] (a : Array α)
    (h : a.toList.Pairwise (· ≤ ·)) (k : α) :
    (binarySearch a k).isSome ↔ k ∈ a :=
  binary_search_correct a h k

/-- A sanity check: searching a sorted array of naturals. -/
example : binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by simp [binarySearch, bsearchAux]

/-- A sanity check: an absent key is not found. -/
example : binarySearch #[1, 3, 5, 7, 9] 4 = none := by simp [binarySearch, bsearchAux]

end CS

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean does not allow a module docstring (`/-! ... -/`) to
precede `import` commands, so this module is written against the Lean core
prelude only (no `import` line at all).  Consequently the order-theoretic
typeclasses used below are the core ones (`Std.IsLinearOrder`,
`Std.LawfulOrderLT`), which Mathlib's `LinearOrder` instances provide
automatically; `RequestProject/LinearOrder.lean` records the Mathlib-flavoured
restatement `CS.binary_search_correct_linearOrder`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
  [Std.IsLinearOrder α] [Std.LawfulOrderLT α]

/-- Binary search for `k` inside the slice `[lo, hi)` of the array `a`.
Returns `some i` when the key was found at index `i`, and `none` otherwise. -/
def bsearchAux (a : Array α) (k : α) (lo hi : Nat) : Option Nat :=
  if lo < hi then
    match a[(lo + hi) / 2]? with
    | none => none
    | some v =>
      if v = k then some ((lo + hi) / 2)
      else if v < k then bsearchAux a k ((lo + hi) / 2 + 1) hi
      else bsearchAux a k lo ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Binary search of the key `k` in the array `a`. -/
def binarySearch (a : Array α) (k : α) : Option Nat := bsearchAux a k 0 a.size

omit [LT α] [DecidableEq α] [DecidableLT α] [Std.LawfulOrderLT α] in
/-- In a sorted array, indexing is monotone. -/
theorem getElem_le_getElem_of_pairwise {a : Array α} (h : a.toList.Pairwise (· ≤ ·))
    {i j : Nat} (hi : i < a.size) (hj : j < a.size) (hij : i ≤ j) : a[i] ≤ a[j] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Std.IsPreorder.le_refl _
  · have := (List.pairwise_iff_getElem.mp h) i j (by simpa using hi) (by simpa using hj) hlt
    simpa using this

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
/-- Soundness: whenever `bsearchAux` returns an index, that index holds the key. -/
theorem bsearchAux_sound (a : Array α) (k : α) (lo hi i : Nat)
    (hres : bsearchAux a k lo hi = some i) : ∃ h : i < a.size, a[i] = k := by
  induction lo, hi using bsearchAux.induct a k generalizing i with
  | case1 lo hi hlt hnone =>
      rw [bsearchAux.eq_def] at hres
      simp [hlt, hnone] at hres
  | case2 lo hi hlt hk =>
      rw [bsearchAux.eq_def] at hres
      simp [hlt, hk] at hres
      obtain ⟨hm, hmk⟩ := Array.getElem?_eq_some_iff.mp hk
      subst hres
      exact ⟨hm, hmk⟩
  | case3 lo hi hlt v hv hne hvk ih =>
      rw [bsearchAux.eq_def] at hres
      simp [hlt, hv, hne, hvk] at hres
      exact ih _ hres
  | case4 lo hi hlt v hv hne hvk ih =>
      rw [bsearchAux.eq_def] at hres
      simp [hlt, hv, hne, hvk] at hres
      exact ih _ hres
  | case5 lo hi hlt =>
      rw [bsearchAux.eq_def] at hres
      simp [hlt] at hres

/-- Completeness: on a sorted array, if the key occurs at some index of the
searched slice, then `bsearchAux` does return an index. -/
theorem bsearchAux_complete (a : Array α) (h : a.toList.Pairwise (· ≤ ·)) (k : α)
    (lo hi : Nat) (hhi : hi ≤ a.size) (j : Nat) (hlo : lo ≤ j) (hj : j < hi)
    (hja : j < a.size) (hjk : a[j] = k) : (bsearchAux a k lo hi).isSome := by
  induction lo, hi using bsearchAux.induct a k generalizing j with
  | case1 lo hi hlt hnone =>
      have hm : a.size ≤ (lo + hi) / 2 := Array.getElem?_eq_none_iff.mp hnone
      omega
  | case2 lo hi hlt hk =>
      rw [bsearchAux.eq_def]
      simp [hlt, hk]
  | case3 lo hi hlt v hv hne hvk ih =>
      obtain ⟨hm, hmv⟩ := Array.getElem?_eq_some_iff.mp hv
      have hnot : ¬ (j ≤ (lo + hi) / 2) := by
        intro hcon
        have hle : a[j] ≤ a[(lo + hi) / 2] :=
          getElem_le_getElem_of_pairwise h hja hm hcon
        rw [hjk, hmv] at hle
        exact ((Std.LawfulOrderLT.lt_iff v k).mp hvk).2 hle
      rw [bsearchAux.eq_def]
      simp only [hlt, hv, hne, hvk, if_true, if_false]
      exact ih hhi j (by omega) hj hja hjk
  | case4 lo hi hlt v hv hne hvk ih =>
      obtain ⟨hm, hmv⟩ := Array.getElem?_eq_some_iff.mp hv
      have hnot : ¬ ((lo + hi) / 2 ≤ j) := by
        intro hcon
        have hle : a[(lo + hi) / 2] ≤ a[j] :=
          getElem_le_getElem_of_pairwise h hm hja hcon
        rw [hjk, hmv] at hle
        have hkv : k ≤ v :=
          Classical.byContradiction fun hkv => hvk ((Std.LawfulOrderLT.lt_iff v k).mpr ⟨hle, hkv⟩)
        exact hne (Std.IsPartialOrder.le_antisymm v k hle hkv)
      rw [bsearchAux.eq_def]
      simp only [hlt, hv, hne, hvk, if_true, if_false]
      exact ih (by omega) j hlo (by omega) hja hjk
  | case5 lo hi hlt => omega

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
/-- Soundness of `binarySearch`: a returned index really points at the key. -/
theorem binary_search_sound (a : Array α) (k : α) {i : Nat} (hi : binarySearch a k = some i) :
    ∃ h : i < a.size, a[i] = k :=
  bsearchAux_sound a k 0 a.size i hi

/-- **Binary search is correct**: on a sorted array, binary search returns an index
if and only if the key is present in the array. -/
theorem binary_search_correct (a : Array α) (h : a.toList.Pairwise (· ≤ ·)) (k : α) :
    (binarySearch a k).isSome ↔ k ∈ a := by
  constructor
  · intro hs
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hlt, heq⟩ := binary_search_sound a k hi
    exact Array.mem_iff_getElem.mpr ⟨i, hlt, heq⟩
  · intro hk
    obtain ⟨j, hj, hjk⟩ := Array.mem_iff_getElem.mp hk
    exact bsearchAux_complete a h k 0 a.size (Nat.le_refl _) j (Nat.zero_le _) hj hj hjk

end CS

