import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace Chem

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma charpoly_Am : Am.charpoly = ∏ l : Fin 10, (Polynomial.X - Polynomial.C (Dv l)) := by
  have hU : (Um : Matrix (Fin 10) (Fin 10) ℂ) = Pm := rfl
  have hUinv : ((Um⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) : Matrix (Fin 10) (Fin 10) ℂ) = Qm := rfl
  have := Matrix.charpoly_units_conj Um (Matrix.diagonal Dv)
  rw [hU, hUinv] at this
  rw [Am_eq_conj, this, Matrix.charpoly_diagonal]

