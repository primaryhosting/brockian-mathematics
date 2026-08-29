/- !
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace BaezDuarte

/-- **Gram nonnegativity (clean self-contained case).**
The Nyman–Beurling / Baez–Duarte distance is a sum of squares of the shape
`‖a • x - b • y‖²`; its scalar core is the quadratic form
`a² - 2ab + b² = (a - b)²`, which is nonnegative. -/

theorem gram_sum_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j * (inner ℝ (v i) (v j) : ℝ) := by
  have key : ∑ i : Fin n, ∑ j : Fin n, c i * c j * (inner ℝ (v i) (v j) : ℝ)
      = (inner ℝ (∑ i : Fin n, c i • v i) (∑ j : Fin n, c j • v j) : ℝ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [key]
  exact real_inner_self_nonneg

end BaezDuarte
end Riemann

