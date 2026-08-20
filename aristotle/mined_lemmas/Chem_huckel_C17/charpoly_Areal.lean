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

namespace Chem

open Polynomial Matrix

/-- The primitive 17-th root of unity `exp (2πi/17)`. -/

lemma charpoly_Areal : Areal.charpoly = ∏ k : Fin 17, (X - C (huckelEigen k)) := by
  have hmap : Polynomial.map (algebraMap ℝ ℂ) Areal.charpoly
      = Polynomial.map (algebraMap ℝ ℂ) (∏ k : Fin 17, (X - C (huckelEigen k))) := by
    rw [← Matrix.charpoly_map, Areal_map, charpoly_A, Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro k _
    simp
  exact Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective hmap

