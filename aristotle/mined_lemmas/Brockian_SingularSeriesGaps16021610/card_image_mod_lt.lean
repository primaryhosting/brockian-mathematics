import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-! ## Admissible tuples and the Hardy–Littlewood singular series

A finite set `H` of nonnegative integers is *admissible* if for every prime `p` the
elements of `H` do not cover all residue classes modulo `p`.  Equivalently, every local
factor of the Hardy–Littlewood singular series attached to `H` is positive.

The main result `Brockian.SingularSeriesGaps16021610` determines exactly which `d` in the
range `1602 ≤ d ≤ 1610` occur as the diameter of a (large) admissible tuple: precisely the
even ones, and for each of those we exhibit an explicit admissible tuple with at least
`145` elements whose smallest element is `0` and whose largest element is `d`.
-/

/-- `H` is an admissible tuple: for each prime `p` some residue class mod `p` is missed. -/

lemma card_image_mod_lt (H : Finset ℕ) (hH : Admissible H) (p : ℕ) (hp : p.Prime) :
    (H.image (fun x => x % p)).card < p := by
  obtain ⟨r, hrp, hr⟩ := hH p hp
  have hsub : H.image (fun x => x % p) ⊆ (Finset.range p).erase r := by
    intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact Finset.mem_erase.mpr ⟨hr x hx, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)⟩
  calc (H.image (fun x => x % p)).card ≤ ((Finset.range p).erase r).card :=
        Finset.card_le_card hsub
    _ < (Finset.range p).card := Finset.card_erase_lt_of_mem (Finset.mem_range.mpr hrp)
    _ = p := Finset.card_range p

/-- Every local factor of the singular series of an admissible tuple is positive. -/
