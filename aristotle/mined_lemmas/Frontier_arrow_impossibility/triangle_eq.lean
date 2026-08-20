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


theorem triangle_eq (huna : Unanimous F) {p q : V} {x y z : Fin 3}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hp : Decisive F p x y) (hq : Decisive F q y z) : p = q := by
  refine Classical.byContradiction (fun hpq => ?_)
  have hyx : y ≠ x := hxy.symm
  have hzx : z ≠ x := hxz.symm
  have hzy : z ≠ y := hyz.symm
  have Lzxy := tri_lt_iff z x y hzx hzy hxy
  have Lyzx := tri_lt_iff y z x hyz hyx hzx
  have h1 : (F (twoProfile (tri y z) (tri z x) q)).lt x y := by
    refine hp _ ?_
    rw [twoProfile_other hpq]
    simp only [Lzxy]
    simp [hxz, hyz]
  have h2 : (F (twoProfile (tri y z) (tri z x) q)).lt y z := by
    refine hq _ ?_
    rw [twoProfile_self]
    simp only [Lyzx]
    simp [hzx, hyz, hzy]
  have h3 : (F (twoProfile (tri y z) (tri z x) q)).lt z x := by
    refine huna _ z x ?_
    intro j
    by_cases hj : j = q
    · subst hj
      rw [twoProfile_self]
      simp only [Lyzx]
      simp [hxy, hzy]
    · rw [twoProfile_other hj]
      simp only [Lzxy]
      simp [hxy, hxz, hzx]
  exact (F (twoProfile (tri y z) (tri z x) q)).asym h3
    ((F (twoProfile (tri y z) (tri z x) q)).tr h1 h2)

/-- **Arrow's theorem (three alternatives).** A unanimous social welfare function
satisfying IIA on three alternatives, with finitely many voters, has a dictator. -/
