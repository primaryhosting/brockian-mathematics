import RequestProject.EulerPolyhedron

/-!
# Fullerene cages have exactly twelve pentagonal faces

A fullerene cage is a polyhedral (spherical) carbon cage in which every atom has exactly three
neighbours and every ring is a pentagon or a hexagon.  Combining Euler's formula
`V - E + F = 2` with the two incidence counts `3V = 2E` and `5p + 6h = 2E` forces the number
of pentagons to be exactly `12`, no matter how many hexagons there are.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### The edge involution -/

omit [Fintype α] in
/-- The edge permutation of a sphere map is an involution. -/

theorem norb_insert_of_fixed {π : Perm α} {D : Finset α} {c : α} (hc : c ∉ D) (hfix : π c = c) :
    norb π (insert c D) = norb π D + 1 := by
  classical
  have hcc : cyc π (insert c D) c = {c} := by
    ext w
    simp only [mem_cyc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hsc⟩
      exact sameCycle_fixed hfix hsc
    · rintro rfl
      exact ⟨Or.inl rfl, SameCycle.refl _ _⟩
  have hz : ∀ z ∈ D, cyc π (insert c D) z = cyc π D z := by
    intro z hzD
    ext w
    simp only [mem_cyc, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hsc⟩
      · exfalso
        have hsc' : π.SameCycle c z := (hw ▸ hsc).symm
        have hzc : z = c := sameCycle_fixed hfix hsc'
        exact hc (hzc ▸ hzD)
      · exact ⟨hw, hsc⟩
    · rintro ⟨hw, hsc⟩
      exact ⟨Or.inr hw, hsc⟩
  have himg : (insert c D).image (cyc π (insert c D)) = insert {c} (D.image (cyc π D)) := by
    rw [Finset.image_insert, hcc]
    congr 1
    exact Finset.image_congr (fun z hz' => hz z hz')
  have hnot : ({c} : Finset α) ∉ D.image (cyc π D) := by
    intro hcon
    obtain ⟨z, hzD, hzc⟩ := Finset.mem_image.1 hcon
    have : z ∈ ({c} : Finset α) := hzc ▸ self_mem_cyc hzD
    rw [Finset.mem_singleton] at this
    exact hc (this ▸ hzD)
  unfold norb
  rw [himg, Finset.card_insert_of_notMem hnot]

/-! ### Summing over the orbits -/

/-- `D` is partitioned by the orbits it meets. -/
