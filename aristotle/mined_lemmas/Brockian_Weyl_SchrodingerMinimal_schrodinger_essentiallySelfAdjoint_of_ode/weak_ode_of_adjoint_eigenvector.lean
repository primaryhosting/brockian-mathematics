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

/-!
## Contents

The first part of this file develops the abstract von Neumann / Weyl deficiency criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space.

The second part constructs the minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain
the smooth compactly supported functions, and shows that it is essentially self-adjoint as soon as
the differential equation `-u'' + V u = ± i u` has no nonzero solution in `L²(ℝ)` (understood in
the distributional sense).
-/

namespace Brockian.Weyl

open LinearPMap Complex

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A partially defined operator `T` on a complex inner product space is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain. -/

theorem weak_ode_of_adjoint_eigenvector {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) (z : ℂ)
    (u : (schrodingerMinimal V hV).adjoint.domain)
    (hu : (schrodingerMinimal V hV).adjoint u = z • (u : L2)) :
    ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, (starRingEnd ℂ) ((u : L2) x) * (-(deriv (deriv g) x) + (V x : ℂ) * g x)
        = (starRingEnd ℂ) z * ∫ x, (starRingEnd ℂ) ((u : L2) x) * g x := by
  intro g hg1 hg2
  set G : testFunctions := ⟨g, show IsTestFn g from ⟨hg1, hg2⟩⟩ with hG
  have hmem : testToL2 G ∈ (schrodingerMinimal V hV).domain := ⟨G, rfl⟩
  have hformal := LinearPMap.adjoint_isFormalAdjoint (dense_domain V hV) u ⟨testToL2 G, hmem⟩
  rw [hu, schrodingerMinimal_apply hV G ⟨testToL2 G, hmem⟩ rfl] at hformal
  rw [inner_smul_left, inner_L2_testToL2, inner_L2_testToL2] at hformal
  exact hformal.symm

