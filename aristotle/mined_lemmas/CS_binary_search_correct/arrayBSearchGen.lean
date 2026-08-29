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

def arrayBSearchGen [Inhabited α] (a : Array α) (key : α) : Option ℕ :=
  bsearchRangeGen (fun i => a[i]!) key 0 a.size

/-- **Binary search is correct** (general version).  On a sorted array over an arbitrary
linear order, binary search returns an index iff the key is present in the array; and any
returned index is a valid index at which the key really occurs. -/
