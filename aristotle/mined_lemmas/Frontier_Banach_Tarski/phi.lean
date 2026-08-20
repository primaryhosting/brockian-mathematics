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

noncomputable def Phi : FreeGroup (Fin 2) →* O3 := FreeGroup.lift gen

/-! ### The integral `3`-adic invariant -/

/-- The effect of a generator (or its inverse) on the integer coordinates `(p, q, r)`
encoding the vector `(p, q√2, r)/3ᵏ`. -/
