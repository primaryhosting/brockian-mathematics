import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def combineStep (w : α → ℝ) (ts : List (HTree α)) : List (HTree α) :=
  match ts.mergeSort (treeLe w) with
  | t1 :: t2 :: rest => HTree.node t1 t2 :: rest
  | _ => ts

