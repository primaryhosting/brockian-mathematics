/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem startsWith_cover_disjoint (i : Fin 2) :
    Disjoint (startsWith (i, true)) ((FreeGroup.of i : F2) • startsWith (i, false)) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨u, hu, rfl⟩
  -- `u` starts with `i⁻¹`, so `i * u` is `u` with its first letter removed
  have hu' : u.toWord.head? = some (i, false) := hu
  obtain ⟨L, hL⟩ : ∃ L, u.toWord = (i, false) :: L := by
    cases hc : u.toWord with
    | nil => rw [hc] at hu'; simp at hu'
    | cons hd tl =>
        rw [hc] at hu'
        simp only [List.head?_cons, Option.some.injEq] at hu'
        exact ⟨tl, by rw [hu']⟩
  have hred : FreeGroup.IsReduced u.toWord := FreeGroup.isReduced_toWord
  rw [hL] at hred
  have hcancel : ((FreeGroup.of i : F2) * u).toWord = L := by
    rw [of_eq_mk]
    exact FreeWord.toWord_cancel (x := (i, true)) (by simpa using hL)
  have hhead : L.head? = some (i, true) := by
    have h2 : ((FreeGroup.of i : F2) * u).toWord.head? = some (i, true) := hw
    rwa [hcancel] at h2
  cases hLc : L with
  | nil => rw [hLc] at hhead; simp at hhead
  | cons hd tl =>
      rw [hLc] at hhead hred
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [FreeGroup.isReduced_cons_cons] at hred
      have hcon := hred.1 (by rw [hhead])
      rw [hhead] at hcon
      simp at hcon

section FreeParadox

variable {X G : Type*} [Group G] [MulAction G X]

/-- **Paradoxicality from a free action.** If the free group of rank two acts on `Y` through
`phi : F2 →* G` in such a way that `Y` is invariant and no nontrivial element of `F2` fixes a
point of `Y`, then `Y` is `G`-paradoxical. -/
