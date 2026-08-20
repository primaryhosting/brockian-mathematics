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

lemma inv_mul_mem_startsWith {i : Fin 2} {g : FreeGroup (Fin 2)}
    (hg : g ∉ startsWith (i, true)) : (FreeGroup.of i)⁻¹ * g ∈ startsWith (i, false) := by
  have h := FreeGroup.startsWith_mk_mul (w := (i, false)) g (by simpa using hg)
  simpa [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev] using h

open FreeGroup in
/-- Multiplying a word starting with `i⁻¹` by `i` never yields a word starting with `i`. -/
