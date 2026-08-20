import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

def istep (x : Fin 2 × Bool) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if x.1 = 0 then
    (if x.2 then (v.1 - 4 * v.2.1, 2 * v.1 + v.2.1, 3 * v.2.2)
     else (v.1 + 4 * v.2.1, -2 * v.1 + v.2.1, 3 * v.2.2))
  else
    (if x.2 then (3 * v.1, v.2.1 - 2 * v.2.2, 4 * v.2.1 + v.2.2)
     else (3 * v.1, v.2.1 + 2 * v.2.2, -4 * v.2.1 + v.2.2))

/-- The integer coordinates of the image of `(0, √2, 0)` under a word. -/
