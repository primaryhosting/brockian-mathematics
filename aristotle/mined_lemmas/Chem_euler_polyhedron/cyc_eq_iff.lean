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

lemma cyc_eq_iff {π : Perm α} {D : Finset α} {x y : α} (hy : y ∈ D) :
    cyc π D x = cyc π D y ↔ π.SameCycle x y := by
  constructor
  · intro h
    have : y ∈ cyc π D x := by rw [h]; exact self_mem_cyc hy
    exact (mem_cyc.1 this).2
  · intro h
    ext z
    simp only [mem_cyc]
    exact and_congr_right fun _ => ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

