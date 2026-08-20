import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem flip_eq {p q : V} {x y : Fin 3} (hxy : x ≠ y)
    (hp : Decisive F p x y) (hq : Decisive F q y x) : p = q := by
  refine Classical.byContradiction (fun hpq => ?_)
  obtain ⟨z, hzx, hzy⟩ : ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by
    clear hp hq; revert hxy; revert x y; decide
  have hyx : y ≠ x := hxy.symm
  have hxz : x ≠ z := hzx.symm
  have hyz : y ≠ z := hzy.symm
  have Lxy := tri_lt_iff x y z hxy hxz hyz
  have Lyx := tri_lt_iff y x z hyx hyz hxz
  have h1 : (F (twoProfile (tri x y) (tri y x) p)).lt x y := by
    refine hp _ ?_
    rw [twoProfile_self]
    simp only [Lxy]
    simp [hxy, hyx, hyz]
  have h2 : (F (twoProfile (tri x y) (tri y x) p)).lt y x := by
    refine hq _ ?_
    rw [twoProfile_other (Ne.symm hpq)]
    simp only [Lyx]
    simp [hxy, hyx, hxz]
  exact (F (twoProfile (tri x y) (tri y x) p)).asym h1 h2

/-- If `p` is decisive for `(x, y)` and `q` is decisive for `(y, z)`, then `p = q`. -/
