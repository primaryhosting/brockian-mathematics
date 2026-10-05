import Mathlib

set_option autoImplicit false

open Finset

/-
  Context module `Brockian.AdmissibilityHLCriterion`.

  The two corpus lemmas `admissible_iff_exists_avoiding_start` and
  `admissible_iff_count_pos` are omitted here because they refer to the auxiliary
  modules `Brockian.AdmissibilityKTuple` / `Brockian.AdmissibilityCriterionScaffold`,
  which are not part of this project; nothing below uses them.
-/

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

theorem mem_residueImage_image_affine (a b : ℤ) (S : Finset ℤ) (p : ℕ) (z : ZMod p) :
    z ∈ residueImage p (S.image (fun x => a * x + b)) ↔
      ∃ x ∈ S, (a : ZMod p) * (x : ZMod p) + (b : ZMod p) = z := by
  simp only [residueImage, Finset.mem_image, Finset.image_image, Function.comp_apply,
    Int.cast_add, Int.cast_mul]

/-- **Affine invariance of admissibility.** For any integers `a`, `b`, the affine image
`a • S + b` of an admissible set `S` is admissible.  If `p ∤ a` the map is a bijection of
`ZMod p`, so the omitted class is transported; if `p ∣ a` the image collapses to the
single class of `b`, which cannot exhaust `ZMod p` since `p ≥ 2`. -/
