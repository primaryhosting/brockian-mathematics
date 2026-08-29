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
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped ComplexConjugate

set_option maxHeartbeats 1000000

namespace Brockian
namespace RiemannScaffold

/-- The nontrivial zeros of the Riemann zeta function: zeros inside the critical strip. -/
def NontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- The *spectral parameter* attached to a point `s` of the critical strip.
It is real exactly when `s` lies on the critical line `Re s = 1/2`. -/
noncomputable def spectralParameter (s : ℂ) : ℂ := (s - 1 / 2) / Complex.I

/-- A *Hilbert–Pólya (Brockian) witness* for `s`: a complex inner product space carrying a
symmetric operator which has the spectral parameter of `s` as an eigenvalue. -/
def HasBrockianWitness (s : ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (T : H →ₗ[ℂ] H) (v : H),
      T.IsSymmetric ∧ v ≠ 0 ∧ T v = spectralParameter s • v

/-- A *Brockian system*: every nontrivial zero of `ζ` admits a Hilbert–Pólya witness, i.e. its
spectral parameter occurs as an eigenvalue of a symmetric operator on a complex inner product
space. This is the Hilbert–Pólya hypothesis in operator-theoretic form. -/
def BrockianSystem : Prop :=
  ∀ s : ℂ, NontrivialZero s → HasBrockianWitness s

/-- Eigenvalues of a symmetric operator on a complex inner product space are real. -/
theorem symmetric_eigenvalue_isReal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) {v : H} (hv : v ≠ 0) {mu : ℂ}
    (hTv : T v = mu • v) : conj mu = mu := by
  have hsym := hT v v
  rw [hTv] at hsym
  rw [inner_smul_left, inner_smul_right] at hsym
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  exact mul_right_cancel₀ hvv hsym

/-- The discharged sub-lemma: a Brockian witness forces the spectral parameter to be real. -/
theorem spectralParameter_isReal_of_hasBrockianWitness
    {s : ℂ} (h : HasBrockianWitness s) : (spectralParameter s).im = 0 := by
  obtain ⟨H, _, _, T, v, hT, hv, hTv⟩ := h
  have h1 : conj (spectralParameter s) = spectralParameter s :=
    symmetric_eigenvalue_isReal hT hv hTv
  have h2 := congrArg Complex.im h1
  simp only [Complex.conj_im] at h2
  linarith

/-- The spectral parameter of `s` is real exactly when `s` lies on the critical line. -/
theorem spectralParameter_im (s : ℂ) : (spectralParameter s).im = 1 / 2 - s.re := by
  simp [spectralParameter, Complex.div_im, Complex.normSq]

/-- **Riemann Hypothesis for a Brockian system.**
If a Brockian (Hilbert–Pólya) system exists, then every nontrivial zero of the Riemann zeta
function lies on the critical line `Re s = 1/2`.  The auxiliary reality sub-lemma is discharged
above, so this statement carries no hypothesis beyond the Brockian system itself. -/
theorem RH_of_BrockianSystem (hB : BrockianSystem) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  intro s hz h0 h1
  have hw : HasBrockianWitness s := hB s ⟨hz, h0, h1⟩
  have him := spectralParameter_isReal_of_hasBrockianWitness hw
  rw [spectralParameter_im] at him
  linarith

/-- Conversely, every point of the critical line admits a Brockian witness (multiplication by a
real scalar on `ℂ`), so the Brockian hypothesis is consistent and is exactly equivalent to RH. -/
theorem hasBrockianWitness_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    HasBrockianWitness s := by
  refine ⟨ℂ, inferInstance, inferInstance, spectralParameter s • LinearMap.id, 1,
    ?_, one_ne_zero, ?_⟩
  · intro x y
    have hre : conj (spectralParameter s) = spectralParameter s := by
      apply Complex.conj_eq_iff_im.mpr
      rw [spectralParameter_im, hs]
      ring
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, inner_smul_left, inner_smul_right,
      hre]
  · simp

/-- The Brockian (Hilbert–Pólya) hypothesis is equivalent to the Riemann Hypothesis. -/
theorem brockianSystem_iff_RH :
    BrockianSystem ↔ ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  constructor
  · exact RH_of_BrockianSystem
  · intro h s hs
    exact hasBrockianWitness_of_re_eq_half (h s hs.1 hs.2.1 hs.2.2)

end RiemannScaffold
end Brockian

