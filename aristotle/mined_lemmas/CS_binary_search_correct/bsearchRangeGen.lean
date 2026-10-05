import Mathlib

/-!
# Binary search over an arbitrary linear order (Mathlib version)

This is the same development as in `RequestProject/Main.lean`, but for arrays over an
arbitrary `LinearOrder`.  The main result is `CS.binary_search_correct_general`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Binary search for `key` in the index range `[lo, hi)` of the "array" `f`. -/

def bsearchRangeGen (f : ℕ → α) (key : α) (lo hi : ℕ) : Option ℕ :=
  if h : lo < hi then
    if f ((lo + hi) / 2) < key then
      bsearchRangeGen f key ((lo + hi) / 2 + 1) hi
    else if key < f ((lo + hi) / 2) then
      bsearchRangeGen f key lo ((lo + hi) / 2)
    else
      some ((lo + hi) / 2)
  else
    none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- If binary search returns an index, that index lies in the search range and the array
really holds `key` there. -/
