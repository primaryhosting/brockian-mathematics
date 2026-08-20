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

theorem toWord_cons {x : α × Bool} {w : FreeGroup α} (h : w.toWord.head? ≠ some (x.1, !x.2)) :
    (FreeGroup.mk [x] * w).toWord = x :: w.toWord := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => simp
  | cons hd tl =>
      rw [hw] at h
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have hne : ¬ (x.1 = hd.1 ∧ x.2 = !hd.2) := by
        rintro ⟨h1, h2⟩
        exact h (by rw [h1, h2]; simp)
      simp [hne]

