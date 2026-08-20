import Mathlib
namespace MS.Foundations

theorem fundamental_theorem_of_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z, p.eval z = 0 :=
  Complex.exists_root hp
