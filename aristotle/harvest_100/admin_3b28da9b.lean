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

/-- A *configuration* of deep-pair data: finitely many species, indexed by `ι`, each
carrying a nonnegative weight and a "deep point" at which the fixed kernel is evaluated. -/
structure Configuration (ι : Type) where
  /-- The nonnegative weight (mass) attached to each species. -/
  weight : ι → ℝ
  /-- The deep point at which the fixed kernel is sampled for each species. -/
  deep : ι → ℝ
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i

/-- The linear charge functional attached to a fixed kernel `R`: the total charge of a
configuration is the `R`-weighted sum over species.  It is linear in the weight vector. -/
noncomputable def charge {ι : Type} [Fintype ι] (R : ℝ → ℝ) (C : Configuration ι) : ℝ :=
  ∑ i, C.weight i * R (C.deep i)

/-- The *termwise* (pointwise-discard) bound that a linear certificate needs in order to
conclude nonnegativity of the charge: every individual species contributes nonnegatively.
This is exactly the step in which a linear certificate discards cross terms. -/
def TermwiseBound {ι : Type} (R : ℝ → ℝ) (C : Configuration ι) : Prop :=
  ∀ i, 0 ≤ C.weight i * R (C.deep i)

/-- A fixed-kernel pointwise-discard linear certificate is *valid* when its termwise bound
holds against every deep-pair configuration, over every finite species set. -/
def Valid (R : ℝ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (C : Configuration ι), TermwiseBound R C

/-- The charge functional is additive in the weight data. -/
theorem charge_add_weight {ι : Type} [Fintype ι] (R : ℝ → ℝ)
    (w₁ w₂ d : ι → ℝ) (h₁ : ∀ i, 0 ≤ w₁ i) (h₂ : ∀ i, 0 ≤ w₂ i) :
    charge R ⟨fun i => w₁ i + w₂ i, d, fun i => add_nonneg (h₁ i) (h₂ i)⟩ =
      charge R ⟨w₁, d, h₁⟩ + charge R ⟨w₂, d, h₂⟩ := by
  simp only [charge, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The charge functional is homogeneous in the weight data. -/
theorem charge_smul_weight {ι : Type} [Fintype ι] (R : ℝ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (w d : ι → ℝ) (h : ∀ i, 0 ≤ w i) :
    charge R ⟨fun i => c * w i, d, fun i => mul_nonneg hc (h i)⟩ =
      c * charge R ⟨w, d, h⟩ := by
  simp only [charge, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The termwise bound implies the certificate's conclusion (nonnegative charge):
this is the "pointwise discard" chain, recorded for completeness. -/
theorem charge_nonneg_of_termwiseBound {ι : Type} [Fintype ι] (R : ℝ → ℝ)
    (C : Configuration ι) (h : TermwiseBound R C) : 0 ≤ charge R C :=
  Finset.sum_nonneg fun i _ => h i

/-- **Fixed kernel + pointwise discard has no slack**: validity of the certificate is
*equivalent* to global nonnegativity of the kernel. -/
theorem valid_iff_kernel_nonneg (R : ℝ → ℝ) : Valid R ↔ ∀ x : ℝ, 0 ≤ R x := by
  constructor
  · intro hV x
    have h := hV (Fin 1) ⟨fun _ => 1, fun _ => x, fun _ => zero_le_one⟩ 0
    simpa using h
  · intro hR ι _ C i
    exact mul_nonneg (C.weight_nonneg i) (hR _)

/-- **Abstract subclass obstruction.**

A fixed-kernel pointwise-discard linear certificate is specified by a single function
`R : ℝ → ℝ` (the kernel), which is used through the per-species linear charging map
`charge R` and whose validity rests on the termwise bound `TermwiseBound R`.

If the analytic continuation of the kernel takes a strictly negative value at some point
`z` (the repaired witness), then the certificate is invalid: there is an explicit
deep-pair configuration — a single species of unit weight placed at `z` — whose termwise
bound fails and whose total charge is strictly negative.  In particular the certificate's
claimed pointwise positivity `∀ x, 0 ≤ R x` cannot hold.

The content is purely the quantifier structure: the kernel is fixed *before* the
configuration is chosen, so one bad deep value already destroys the whole subclass. -/
theorem subclass_obstruction_statement (R : ℝ → ℝ) (z : ℝ) (hz : R z < 0) :
    ¬ Valid R ∧
      ¬ (∀ x : ℝ, 0 ≤ R x) ∧
      ∃ C : Configuration (Fin 1),
        (¬ TermwiseBound R C) ∧ charge R C < 0 := by
  have hnn : ¬ (∀ x : ℝ, 0 ≤ R x) := fun h => absurd (h z) (not_le.mpr hz)
  refine ⟨fun hV => hnn ((valid_iff_kernel_nonneg R).mp hV), hnn, ?_⟩
  refine ⟨⟨fun _ => 1, fun _ => z, fun _ => zero_le_one⟩, ?_, ?_⟩
  · exact fun h => absurd (by simpa using h 0) (not_le.mpr hz)
  · simp [charge, hz]

end Zeta23Obstruction

