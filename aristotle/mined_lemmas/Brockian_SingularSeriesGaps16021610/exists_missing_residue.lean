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

lemma exists_missing_residue (H : Finset ℕ) (p : ℕ) (h : H.card < p) :
    ∃ r < p, ∀ x ∈ H, x % p ≠ r := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le _) h
  have hsub : H.image (fun x => x % p) ⊆ Finset.range p := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨x, _, rfl⟩ := hr
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  have hcard : (H.image (fun x => x % p)).card < (Finset.range p).card := by
    have := Finset.card_image_le (s := H) (f := fun x => x % p)
    simpa using lt_of_le_of_lt this h
  obtain ⟨r, hr, hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  intro x hx hxr
  exact hr' (Finset.mem_image.mpr ⟨x, hx, hxr⟩)

/-- The number of residues occupied by an admissible tuple mod a prime `p` is `< p`. -/
