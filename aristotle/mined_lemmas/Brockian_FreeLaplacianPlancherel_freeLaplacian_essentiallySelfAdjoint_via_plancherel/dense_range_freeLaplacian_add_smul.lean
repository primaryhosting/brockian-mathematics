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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.FreeLaplacianPlancherel

open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

/-- Euclidean space `ℝ^d`, the configuration space of the free Laplacian. -/
abbrev Eucl (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev L2 (d : ℕ) := Lp (α := Eucl d) ℂ 2 volume

/-- A Schwartz function, viewed as an element of `L²(ℝ^d)`. The Schwartz space is the core
(dense domain) on which we consider the free Laplacian. -/

theorem dense_range_freeLaplacian_add_smul {d : ℕ} (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun f : 𝓢(Eucl d, ℂ) => freeLaplacian f + z • toL2 f)) := by
  rw [range_shiftMap, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  have horth : ∀ f : 𝓢(Eucl d, ℂ), inner ℂ (freeLaplacian f + z • toL2 f) u = 0 := by
    intro f
    exact hu _ ⟨f, rfl⟩
  have key := integral_conj_mul_symbol_eq_zero z u horth
  -- On the Fourier side, `u` is annihilated by multiplication by a nowhere vanishing symbol.
  set v : Eucl d → ℂ := ((𝓕 u : L2 d) : Eucl d → ℂ) with hvdef
  set c : Eucl d → ℂ := fun ξ => (symbol ξ : ℂ) + (starRingEnd ℂ) z with hc
  have hccont : Continuous c := by simp only [hc, symbol]; fun_prop
  have hcne : ∀ ξ, c ξ ≠ 0 := by
    intro ξ h
    apply hz
    have him : (c ξ).im = -z.im := by simp [hc]
    rw [h] at him
    simpa using him
  have hvloc : LocallyIntegrable v volume := (Lp.memLp (𝓕 u)).locallyIntegrable one_le_two
  have hwloc : LocallyIntegrable (fun ξ => c ξ * v ξ) volume := by
    rw [← locallyIntegrableOn_univ] at hvloc ⊢
    exact hvloc.continuousOn_mul hccont.continuousOn isClosed_univ.isLocallyClosed
  have hw : ∀ᵐ ξ, c ξ * v ξ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hwloc
    intro φ hsm hcs
    have hcs' : HasCompactSupport (fun x : Eucl d => ((φ x : ℝ) : ℂ)) :=
      HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hcs (by simp)
    have hsm' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Eucl d => ((φ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hsm
    have hkey := key (hcs'.toSchwartzMap hsm')
    simp only [HasCompactSupport.toSchwartzMap_toFun, Complex.conj_ofReal] at hkey
    rw [← hkey]
    apply integral_congr_ae
    filter_upwards with ξ
    simp [Complex.real_smul, hc]
  have hvzero : ∀ᵐ ξ, v ξ = 0 := by
    filter_upwards [hw] with ξ hξ
    rcases mul_eq_zero.mp hξ with h | h
    · exact absurd h (hcne ξ)
    · exact h
  have hFu : (𝓕 u : L2 d) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hvzero] with ξ hξ
    simpa [hvdef] using hξ
  have hnorm : ‖u‖ = 0 := by rw [← Lp.norm_fourier_eq u, hFu, norm_zero]
  simpa using norm_eq_zero.mp hnorm

/-- **The free Laplacian is essentially self-adjoint on the Schwartz core**, proved via
Plancherel's theorem.

The three conjuncts are exactly the basic criterion for essential self-adjointness of the
symmetric operator `-Δ` with domain the Schwartz space `𝓢(ℝ^d)` inside `L²(ℝ^d)`:

* the domain is dense in `L²(ℝ^d)`;
* the operator is symmetric on that domain;
* for every non-real `z` (in particular `z = ±i`) the range of `-Δ + z` is dense, i.e. both
  deficiency subspaces of the closure of `-Δ` are trivial.
-/
