/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- On a simply connected, locally path connected space, every continuous nowhere-vanishing
complex-valued function has a continuous logarithm.  This is the lifting property of the
covering map `exp : ℂ → ℂ \ {0}`. -/

theorem exists_continuous_clog {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocPathConnectedSpace A] [Nonempty A] (F : A → ℂ) (hF : Continuous F) (h0 : ∀ a, F a ≠ 0) :
    ∃ L : A → ℂ, Continuous L ∧ ∀ a, Complex.exp (L a) = F a := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  obtain ⟨L, ⟨-, hL⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨F, hF⟩ : C(A, ℂ)) (e₀ := Complex.log (F a₀)) (Complex.exp_log (h0 a₀)) (fun a => h0 a)
  exact ⟨L, L.continuous, fun a => congrFun hL a⟩

/-- A nonzero complex number with nonnegative real part lies in the slit plane. -/
