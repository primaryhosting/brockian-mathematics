import Mathlib

/-!
# A coefficient firewall between finite phase depth and real de Rham data

The phase-depth cocycles in this repository use the additive coefficient group `ZMod 5`.
Ordinary de Rham cochains use real (or characteristic-zero) vector spaces.  These coefficient
systems cannot be silently identified: every additive homomorphism from `ZMod 5` to `ℝ` is zero.

This is deliberately a no-go theorem, not a comparison theorem.  A useful geometric realization
must instead retain the torsion, for example through fifth-root-valued flat holonomy.
-/

namespace Brockian.FiniteToDeRhamNoGo

/-- Every additive coefficient map from `ZMod 5` to the reals is zero. -/
theorem addMonoidHom_zmod5_real_eq_zero (f : ZMod 5 →+ ℝ) : f = 0 := by
  ext x
  have hx : (5 : ℕ) • f x = 0 := by
    rw [← f.map_nsmul]
    norm_num
  norm_num at hx ⊢
  exact hx

/-- In particular, there is no injective additive coefficient map `ZMod 5 → ℝ`. -/
theorem not_exists_injective_addMonoidHom_zmod5_real :
    ¬ ∃ f : ZMod 5 →+ ℝ, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hzero := congrFun (addMonoidHom_zmod5_real_eq_zero f) (1 : ZMod 5)
  have : (1 : ZMod 5) = 0 := hf (by simpa using hzero)
  norm_num at this

end Brockian.FiniteToDeRhamNoGo
