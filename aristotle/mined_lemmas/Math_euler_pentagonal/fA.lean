/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

def fA (S : Finset ℕ) : Finset ℕ :=
  ((S.erase (mn S)) \ Finset.Icc (mx S + 1 - mn S) (mx S)) ∪
    Finset.Icc (mx S + 2 - mn S) (mx S + 1)

/-- Franklin's move when the smallest part exceeds the staircase length:
subtract one from each of the `σ` largest parts and adjoin a new part `σ`. -/
