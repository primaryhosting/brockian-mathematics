import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a
module, so the mandated header comment is placed immediately after the import.
-/

open scoped BigOperators ContDiff

namespace Frontier

namespace NavierStokes

/-- Points/vectors of `ℝ³`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem navier_stokes_shear_reduction (nu : ℝ) (v : ℝ → Vec → ℝ) (hv : SmoothST v)
    (hindep : ∀ (t : ℝ) (x : Vec) (s : ℝ), v t (Function.update x 0 s) = v t x)
    (hheat : ∀ t x, deriv (fun s => v s x) t = nu * laplacian (v t) x) :
    IsGlobalSmoothSolution nu (fun t x => Pi.single 0 (v t x)) (fun _ _ => 0) := by
  have hd0 : ∀ (t : ℝ) (x : Vec), pderiv (v t) 0 x = 0 := fun t x =>
    pderiv_eq_zero_of_indep _ 0 x ((hv.spatial t) x) (hindep t x)
  have hc0 : ∀ t : ℝ, (fun y : Vec => (Pi.single (0 : Fin 3) (v t y) : Vec) 0) = v t := by
    intro t; funext y; simp
  have hcne : ∀ (t : ℝ) (j : Fin 3), j ≠ 0 →
      (fun y : Vec => (Pi.single (0 : Fin 3) (v t y) : Vec) j) = fun _ : Vec => (0 : ℝ) := by
    intro t j hj; funext y; simp [hj]
  refine ⟨?_, contDiff_const, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · subst hj
      have h : (fun q : ℝ × Vec => (Pi.single (0 : Fin 3) (v q.1 q.2) : Vec) 0)
          = fun q : ℝ × Vec => v q.1 q.2 := by funext q; simp
      show ContDiff ℝ ∞ _
      rw [h]
      exact hv
    · have h : (fun q : ℝ × Vec => (Pi.single (0 : Fin 3) (v q.1 q.2) : Vec) j)
          = fun _ : ℝ × Vec => (0 : ℝ) := by funext q; simp [hj]
      show ContDiff ℝ ∞ _
      rw [h]
      exact contDiff_const
  · intro t x
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      rw [hc0 t]
      exact hd0 t x
    · rw [hcne t i hi]
      exact pderiv_const 0 i x
  · intro t x j
    by_cases hj : j = 0
    · subst hj
      have hconv : convective (fun t x => Pi.single 0 (v t x)) t x 0 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [hc0 t, hd0 t x]
          ring
        · simp [hi]
      have hderiv : deriv (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) 0) t
          = deriv (fun s => v s x) t := by
        have he : (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) 0)
            = fun s : ℝ => v s x := by funext s; simp
        rw [he]
      rw [hconv, hderiv, hc0 t, pderiv_const, hheat t x]
      ring
    · have hconv : convective (fun t x => Pi.single 0 (v t x)) t x j = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hcne t j hj, pderiv_const]
        ring
      have hderiv : deriv (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) j) t = 0 := by
        have he : (fun s : ℝ => (Pi.single (0 : Fin 3) (v s x) : Vec) j)
            = fun _ : ℝ => (0 : ℝ) := by funext s; simp [hj]
        rw [he]
        simp
      rw [hconv, hderiv, hcne t j hj, laplacian_const, pderiv_const]
      ring

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

