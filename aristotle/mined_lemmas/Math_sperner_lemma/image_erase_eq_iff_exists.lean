import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` lines to come first in a module, so the
required header block is placed immediately after the single `import Mathlib` line.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Codimension-one subsets -/

/-- Subsets of `S` of cardinality `S.card - 1` are exactly the sets `S.erase x` for `x ∈ S`;
hence counting them amounts to counting the vertices `x ∈ S` with the corresponding property. -/

lemma image_erase_eq_iff_exists {color : V → ℕ} {S : Finset V} {x : V} (hx : x ∈ S) :
    (S.erase x).image color = S.image color ↔ ∃ y ∈ S, y ≠ x ∧ color y = color x := by
  constructor
  · intro h
    have hmem : color x ∈ (S.erase x).image color := by
      rw [h]; exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hyc⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_erase] at hy
    exact ⟨y, hy.2, hy.1, hyc⟩
  · rintro ⟨y, hyS, hyx, hyc⟩
    refine Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _)) ?_
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
    by_cases hzx : z = x
    · subst hzx
      exact Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hyS⟩, hyc⟩
    · exact Finset.mem_image.2 ⟨z, Finset.mem_erase.2 ⟨hzx, hz⟩, rfl⟩

/-! ### The door-counting lemma -/

/-- **Door counting.**  Let `S` be a cell with `k+2` vertices whose colours lie in
`{0, …, k+1}`.  The number of codimension-one faces of `S` whose colour set is exactly
`{0, …, k}` (the "doors" of `S`) is odd precisely when `S` is rainbow. -/
