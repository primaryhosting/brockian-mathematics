/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

def fB (S : Finset ℕ) : Finset ℕ :=
  insert (stair S)
    ((S \ Finset.Icc (mx S + 1 - stair S) (mx S)) ∪ Finset.Icc (mx S - stair S) (mx S - 1))

/-- Franklin's involution. -/
