import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  -- the reduced word of `w`
  set L := w.toWord with hL
  have hLne : L ≠ [] := by
    simp only [hL, ne_eq, FreeGroup.toWord_eq_nil_iff]
    exact hne
  obtain ⟨x, L', hx⟩ : ∃ x L', L = x :: L' := by
    cases hcase : L with
    | nil => exact absurd hcase hLne
    | cons a l => exact ⟨a, l, rfl⟩
  have hred : FreeGroup.IsReduced L := by rw [hL]; exact FreeGroup.isReduced_toWord
  have hmk : FreeGroup.mk L = w := by rw [hL]; exact FreeGroup.mk_toWord
  -- the matrix of `w` is the identity
  have hmat : (L.map letterMat).prod = 1 := by
    rw [← rho_mk, hmk, hw]
    rfl
  -- hence the integral vector is `5 ^ n • v0`
  have hveq : (fun i => ((iv L i : ℤ) : ℝ)) = fun i => ((5 : ℝ) ^ L.length * ((v0 i : ℤ) : ℝ)) := by
    rw [show (fun i => ((iv L i : ℤ) : ℝ)) = ivR L from rfl, ← prod_mulVec, hmat]
    funext i
    simp [Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  have hint : ∀ i, iv L i = 5 ^ L.length * v0 i := by
    intro i
    have := congrFun hveq i
    have h2 : ((iv L i : ℤ) : ℝ) = (((5 ^ L.length * v0 i : ℤ)) : ℝ) := by
      rw [this]; push_cast; ring
    exact_mod_cast h2
  have hzero : ivm L = 0 := by
    funext i
    have : iv L i = 5 ^ L.length * v0 i := hint i
    simp only [ivm, this, Pi.zero_apply]
    push_cast
    have h5 : ((5 : ZMod 5)) = 0 := by decide
    rw [h5]
    have : L.length ≠ 0 := by
      rw [hx]; simp
    rw [zero_pow this, zero_mul]
  obtain ⟨c, hc, hcv⟩ := ivm_invariant L' x (by rw [← hx]; exact hred)
  rw [← hx, hzero] at hcv
  have : uu x = 0 := by
    have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    have := congrArg (fun v : Fin 3 → ZMod 5 => c⁻¹ • v) hcv.symm
    simpa [smul_smul, hcinv] using this
  exact uu_ne_zero x this

end FreeRotations

end Frontier

/-
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.FreeRotations

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Set Function

/-! ## The action of `SO(3)` by isometries of `ℝ³` -/

namespace Sphere

open Matrix FreeRotations

/-- Euclidean three-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of isometries of `ℝ³`, as a subgroup of the group of permutations. -/
