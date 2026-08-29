import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma card_shell_le (hd : d ≤ 2) (M r : ℕ) (hr : 1 ≤ r) :
    ((box d M).filter fun x => snorm x = r).card ≤ 8 * r := by
  classical
  have hsub : ((box d M).filter fun x => snorm x = r) ⊆ box d r \ box d (r - 1) := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [Finset.mem_sdiff, mem_box_iff, mem_box_iff]
    exact ⟨le_of_eq hx.2, by omega⟩
  have hcard := Finset.card_le_card hsub
  have hinter : box d (r - 1) ∩ box d r = box d (r - 1) :=
    Finset.inter_eq_left.2 (box_subset (by omega))
  have hsd : (box d r \ box d (r - 1)).card = (2 * r + 1) ^ d - (2 * (r - 1) + 1) ^ d := by
    rw [Finset.card_sdiff, hinter, card_box, card_box]
  rw [hsd] at hcard
  have hkey : (2 * r + 1) ^ d - (2 * (r - 1) + 1) ^ d ≤ 8 * r := by
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    interval_cases d
    · simp
    · simp only [pow_one]
      omega
    · have e1 : (2 * (n + 1) + 1) ^ 2 = 4 * (n * n) + 12 * n + 9 := by ring
      have e2 : (2 * n + 1) ^ 2 = 4 * (n * n) + 4 * n + 1 := by ring
      rw [e1, e2]
      generalize n * n = k
      omega
  omega

/-- The harmonic-type sum over the box, obtained by summing over the spheres. -/
