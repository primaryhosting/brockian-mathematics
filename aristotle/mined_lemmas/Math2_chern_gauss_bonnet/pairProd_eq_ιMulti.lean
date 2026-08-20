/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/

theorem pairProd_eq_ιMulti (m : ℕ) (v : Fin (2 * m) → V) :
    pairProd m v = ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
  classical
  set A : ℕ → ExteriorAlgebra ℝ V :=
    fun j => if h : j < 2 * m then ExteriorAlgebra.ι ℝ (v ⟨j, h⟩) else 1 with hA
  have hAval : ∀ i : Fin (2 * m), A i.1 = ExteriorAlgebra.ι ℝ (v i) := by
    intro i; simp only [hA, dif_pos i.2]
  have h1 : pairProd m v = ((List.range m).map (fun i => A (2 * i) * A (2 * i + 1))).prod := by
    rw [list_prod_range_eq_ofFn]
    simp only [pairProd, curvForm]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    show _ = A (pairFst m i).1 * A (pairSnd m i).1
    rw [hAval (pairFst m i), hAval (pairSnd m i)]
  rw [h1, prod_range_pairs, list_prod_range_eq_ofFn, ExteriorAlgebra.ιMulti_apply]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hAval i))

