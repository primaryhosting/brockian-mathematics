/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

namespace Zeta23Obstruction

/-- A **configuration** of deep points: finitely many species, each carrying a real
"deep point" `pt i` and a strictly positive weight `wt i`. -/
structure DeepConfig where
  /-- number of species -/
  n : ℕ
  /-- the deep point attached to each species -/
  pt : Fin n → ℝ
  /-- the (strictly positive) weight attached to each species -/
  wt : Fin n → ℝ
  /-- positivity of the weights -/
  wt_pos : ∀ i : Fin n, 0 < wt i

/-- The **linear charge** of a configuration relative to a fixed kernel `R`:
the linear functional `c ↦ ∑ᵢ wᵢ · R(zᵢ)` obtained by per-species linear charging. -/

theorem not_certificateValidAll (R : ℝ → ℝ) (z : ℝ) (hz : R z < 0) :
    ¬ CertificateValidAll R := by
  intro hvalid
  refine termwiseNonneg_fails_of_negative_point R
    ⟨1, fun _ => z, fun _ => 1, fun _ => one_pos⟩ ⟨0, one_pos⟩ ?_ (hvalid _)
  simpa using hz

/-- Corollary: a globally nonnegative kernel can never agree with the continued kernel,
so the "fixed kernel with `∀ x, 0 ≤ R x`" hypothesis of the certificate is unattainable
once a single bad deep value exists. -/
