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

theorem norb_swap_mul_of_not_sameCycle {π : Perm α} {D : Finset α} {x y : α}
    (hx : x ∈ D) (hy : y ∈ D) (hxy : ¬ π.SameCycle x y) :
    norb (swap x y * π) D + 1 = norb π D := by
  classical
  set In : α → Prop := fun z => π.SameCycle z x ∨ π.SameCycle z y with hIn
  set Din : Finset α := D.filter In with hDin
  set Dout : Finset α := D.filter (fun z => ¬ In z) with hDout
  set S : Finset (Finset α) := Dout.image (cyc π D) with hS
  have hsplit : Din ∪ Dout = D := Finset.filter_union_filter_not_eq _ _
  have himg : ∀ f : α → Finset α, D.image f = Din.image f ∪ Dout.image f := by
    intro f; rw [← Finset.image_union, hsplit]
  have hxDin : x ∈ Din := Finset.mem_filter.2 ⟨hx, Or.inl (SameCycle.refl _ _)⟩
  have hyDin : y ∈ Din := Finset.mem_filter.2 ⟨hy, Or.inr (SameCycle.refl _ _)⟩
  -- (1) outside the two cycles nothing changes
  have h1 : ∀ z ∈ Dout, cyc (swap x y * π) D z = cyc π D z := by
    intro z hz
    have hznot : ¬ In z := (Finset.mem_filter.1 hz).2
    ext w
    simp only [mem_cyc, sameCycle_swap_mul_iff hxy, MergeRel]
    constructor
    · rintro ⟨hwD, hrel | ⟨hzin, -⟩⟩
      · exact ⟨hwD, hrel⟩
      · exact absurd hzin hznot
    · rintro ⟨hwD, hrel⟩
      exact ⟨hwD, Or.inl hrel⟩
  -- (2) the merged class
  have h2 : ∀ z ∈ Din, cyc (swap x y * π) D z = Din := by
    intro z hz
    have hzin : In z := (Finset.mem_filter.1 hz).2
    ext w
    simp only [mem_cyc, sameCycle_swap_mul_iff hxy, MergeRel, hDin, Finset.mem_filter]
    constructor
    · rintro ⟨hwD, hrel | ⟨-, hwin⟩⟩
      · refine ⟨hwD, ?_⟩
        rcases hzin with h | h
        · exact Or.inl (hrel.symm.trans h)
        · exact Or.inr (hrel.symm.trans h)
      · exact ⟨hwD, hwin⟩
    · rintro ⟨hwD, hwin⟩
      exact ⟨hwD, Or.inr ⟨hzin, hwin⟩⟩
  -- (3) classes of the new permutation
  have h3 : D.image (cyc (swap x y * π) D) = insert Din S := by
    rw [himg]
    have e1 : Din.image (cyc (swap x y * π) D) = {Din} := by
      rw [Finset.image_congr (g := fun _ => Din) (fun z hz => h2 z hz),
        Finset.image_const ⟨x, hxDin⟩]
    have e2 : Dout.image (cyc (swap x y * π) D) = S := by
      rw [hS]; exact Finset.image_congr (fun z hz => h1 z hz)
    rw [e1, e2]
    ext C
    simp [Finset.mem_insert]
  -- (4) classes of the old permutation
  have h4 : D.image (cyc π D) = insert (cyc π D x) (insert (cyc π D y) S) := by
    rw [himg]
    have : Din.image (cyc π D) = {cyc π D x, cyc π D y} := by
      apply Finset.Subset.antisymm
      · intro C hC
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hC
        rcases (Finset.mem_filter.1 hz).2 with h | h
        · exact Finset.mem_insert.2 (Or.inl (cyc_eq_of_sameCycle h))
        · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (cyc_eq_of_sameCycle h)))
      · intro C hC
        rcases Finset.mem_insert.1 hC with rfl | hC
        · exact Finset.mem_image.2 ⟨x, hxDin, rfl⟩
        · rw [Finset.mem_singleton.1 hC]
          exact Finset.mem_image.2 ⟨y, hyDin, rfl⟩
    rw [this]
    ext C
    simp [Finset.mem_insert, hS, Finset.mem_image]
  -- (5) the classes involved are distinct and not among the untouched ones
  have hmemS : ∀ C ∈ S, ∃ z ∈ Dout, cyc π D z = C := by
    intro C hC
    obtain ⟨z, hz, hzC⟩ := Finset.mem_image.1 hC
    exact ⟨z, hz, hzC⟩
  have hDinS : Din ∉ S := by
    intro hcon
    obtain ⟨z, hz, hzC⟩ := hmemS _ hcon
    have hzD : z ∈ D := (Finset.mem_filter.1 hz).1
    have : z ∈ Din := hzC ▸ self_mem_cyc hzD
    exact (Finset.mem_filter.1 hz).2 (Finset.mem_filter.1 this).2
  have hCxS : cyc π D x ∉ S := by
    intro hcon
    obtain ⟨z, hz, hzC⟩ := hmemS _ hcon
    have hzD : z ∈ D := (Finset.mem_filter.1 hz).1
    have hzx : π.SameCycle z x := (cyc_eq_iff hx).1 (by rw [hzC])
    exact (Finset.mem_filter.1 hz).2 (Or.inl hzx)
  have hCyS : cyc π D y ∉ S := by
    intro hcon
    obtain ⟨z, hz, hzC⟩ := hmemS _ hcon
    have hzD : z ∈ D := (Finset.mem_filter.1 hz).1
    have hzy : π.SameCycle z y := (cyc_eq_iff hy).1 (by rw [hzC])
    exact (Finset.mem_filter.1 hz).2 (Or.inr hzy)
  have hCxy : cyc π D x ≠ cyc π D y := fun hcon => hxy ((cyc_eq_iff hy).1 hcon)
  -- conclude
  unfold norb
  rw [h3, h4, Finset.card_insert_of_notMem hDinS,
    Finset.card_insert_of_notMem (by simp [Finset.mem_insert, hCxy, hCxS]),
    Finset.card_insert_of_notMem hCyS]

/-- If `x` and `y` lie in the same `π`-cycle, that cycle is cut into two by `swap x y * π`,
and in particular `x` and `y` are no longer in the same cycle. -/
