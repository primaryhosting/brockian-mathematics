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

def arrayBSearch (a : Array Int) (key : Int) : Option Nat :=
  bsearchRange (fun i => a[i]!) key 0 a.size

/-- **Binary search is correct.**  On a sorted array, binary search returns an index if and
only if the key is present in the array; moreover, whenever it returns an index, that index is
a valid index of the array at which the key really occurs. -/
