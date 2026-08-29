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

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of an eigenvalue sequence `lam : ℕ → ℝ`:
`spectralCounting lam Λ` is the number of indices `n` with `lam n ≤ Λ`
(taken as `0` when that index set is infinite). -/
noncomputable def spectralCounting (lam : ℕ → ℝ) (Λ : ℝ) : ℕ :=
  {n : ℕ | lam n ≤ Λ}.ncard

/-- Discreteness of the spectrum: only finitely many eigenvalues lie below any level `Λ`,
so that the counting function is genuinely a cardinality. -/
def SpectrumDiscrete (lam : ℕ → ℝ) : Prop :=
  ∀ Λ : ℝ, {n : ℕ | lam n ≤ Λ}.Finite

/-- Weyl-law asymptotics of exponent `d` with (positive) Weyl constant `C`:
`spectralCounting lam Λ / Λ ^ (d / 2) → C` as `Λ → ∞`. -/
def WeylLawMatch (lam : ℕ → ℝ) (d C : ℝ) : Prop :=
  Tendsto (fun Λ : ℝ => (spectralCounting lam Λ : ℝ) / Λ ^ (d / 2)) atTop (𝓝 C)

/-- For `d > 0` the Weyl scaling factor `Λ ^ (d / 2)` diverges. -/
theorem tendsto_weyl_scale_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (fun Λ : ℝ => Λ ^ (d / 2)) atTop atTop :=
  Real.tendsto_rpow_atTop (by linarith)

/-- **Counting diverges from discreteness and a matching Weyl law.**

If the spectrum is discrete and its counting function matches a Weyl law
`N(Λ) ∼ C · Λ ^ (d / 2)` with positive exponent `d` and positive Weyl constant `C`,
then the counting function diverges to infinity.

(The discreteness hypothesis is what makes `spectralCounting` the honest cardinality of the
set of eigenvalues below `Λ`; the asymptotic argument itself only uses the Weyl law.) -/
theorem counting_diverges_of_discrete_and_WeylLawMatch
    (lam : ℕ → ℝ) (d C : ℝ) (hd : 0 < d) (hC : 0 < C)
    (_hdisc : SpectrumDiscrete lam) (hweyl : WeylLawMatch lam d C) :
    Tendsto (fun Λ : ℝ => (spectralCounting lam Λ : ℝ)) atTop atTop := by
  have hmul :
      Tendsto (fun Λ : ℝ => ((spectralCounting lam Λ : ℝ) / Λ ^ (d / 2)) * Λ ^ (d / 2))
        atTop atTop :=
    hweyl.mul_atTop hC (tendsto_weyl_scale_atTop hd)
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  have hne : Λ ^ (d / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hΛ _)
  exact div_mul_cancel₀ _ hne

end Brockian.Weyl.WeylLawTarget

