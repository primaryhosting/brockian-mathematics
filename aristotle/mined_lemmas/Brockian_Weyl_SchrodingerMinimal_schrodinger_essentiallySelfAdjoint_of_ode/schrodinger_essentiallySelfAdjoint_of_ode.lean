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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem schrodinger_essentiallySelfAdjoint_of_ode (V₀ : ℝ) :
    (∀ f g : ℝ → ℂ, IsTestFunction f → IsTestFunction g →
        ∫ x, (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x
          = ∫ x, (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x)
    ∧ (∀ z : ℂ, z.im ≠ 0 → ∀ w : ℝ → ℂ, MemLp w 2 volume → ∀ ε : ℝ, 0 < ε →
        ∃ f : ℝ → ℂ, IsTestFunction f ∧
          eLpNorm (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume
            < ENNReal.ofReal ε) :=
  ⟨fun _ _ hf hg => schrodinger_symmetric V₀ hf hg,
   fun _ hz _ hw _ hε => schrodinger_range_dense V₀ hz hw hε⟩

end Brockian.Weyl.SchrodingerMinimal

