import Mathlib
import Brockian.RiemannScaffold

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
#print axioms Brockian.RiemannScaffold.RH_of_BrockianSystem
#print axioms Brockian.RiemannScaffold.nonempty_brockianSystem_iff_RH

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

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Brockian
namespace RiemannScaffold

/-! ## The Brockian system and the critical-line theorem -/

/-- A *nontrivial zero* of the Riemann zeta function: a zero lying in the open critical
strip `0 < Re s < 1`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- The Riemann Hypothesis, in the form used here: every nontrivial zero of `ζ` lies on the
critical line. -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

/-- A **Brockian system** on a complex inner product space `H` is a Hilbert–Pólya datum:
a symmetric (formally self-adjoint) linear operator `T` on `H` together with, for every
nontrivial zero `s` of `ζ`, a nonzero eigenvector of `T` with eigenvalue `-i (s - 1/2)`
(the spectral parameter attached to `s` by the critical-line normalisation). -/
structure BrockianSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Brockian operator. -/
  T : H →ₗ[ℂ] H
  /-- `T` is symmetric for the inner product of `H`. -/
  selfAdjoint : ∀ x y : H, inner ℂ (T x) y = inner ℂ x (T y)
  /-- Every nontrivial zero of `ζ` is realised as an eigenvalue of `T`, via the
  normalisation `s ↦ -i (s - 1/2)`. -/
  spectral : ∀ s : ℂ, IsNontrivialZero s →
    ∃ v : H, v ≠ 0 ∧ T v = (-Complex.I * (s - 1 / 2)) • v

/-- **Riemann Hypothesis from a Brockian system.**
If a Brockian system exists on some complex inner product space, then every nontrivial
zero of the Riemann zeta function lies on the critical line `Re s = 1/2`.

The proof is the Hilbert–Pólya mechanism: a symmetric operator has real eigenvalues (the
eigenvalue equation together with symmetry forces `conj λ = λ` after cancelling the
nonzero factor `⟪v, v⟫`), and `-i (s - 1/2)` is real exactly when `Re s = 1/2`. -/
theorem RH_of_BrockianSystem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : BrockianSystem H) : ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 := by
  intro s hs
  obtain ⟨v, hv, hTv⟩ := B.spectral s hs
  set lam : ℂ := -Complex.I * (s - 1 / 2) with hlam
  have h1 : inner ℂ (B.T v) v = conj lam * inner ℂ v v := by
    rw [hTv, inner_smul_left]
  have h2 : inner ℂ v (B.T v) = lam * inner ℂ v v := by
    rw [hTv, inner_smul_right]
  have h3 : conj lam * (inner ℂ v v : ℂ) = lam * inner ℂ v v := by
    rw [← h1, ← h2, B.selfAdjoint]
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have h4 : conj lam = lam := mul_right_cancel₀ hvv h3
  have h5 : lam.im = 0 := Complex.conj_eq_iff_im.mp h4
  have h6 : lam.im = -(s.re - 1 / 2) := by simp [hlam]
  rw [h6] at h5
  linarith

/-- Consequence of `RH_of_BrockianSystem` in the right half-plane: given a Brockian system,
every zero of `ζ` with positive real part lies on the critical line. (Zeros with
`Re s ≥ 1` are excluded unconditionally by the classical non-vanishing theorem, available
in Mathlib as `riemannZeta_ne_zero_of_one_le_re`.) -/
theorem criticalLine_of_BrockianSystem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (B : BrockianSystem H) (s : ℂ) (hs : 0 < s.re)
    (hz : riemannZeta s = 0) : s.re = 1 / 2 := by
  by_cases h1 : s.re < 1
  · exact RH_of_BrockianSystem B s ⟨hz, hs, h1⟩
  · exact absurd hz (riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1))

/-! ## Non-vacuity: a canonical space carrying a Brockian system exactly under RH

To show that the hypothesis of `RH_of_BrockianSystem` is not vacuous (and to pin down
exactly how strong it is), we build a canonical inner product space — the algebraic span of
the standard orthonormal family in `ℓ²` indexed by the nontrivial zeros — and show that it
carries a Brockian system if and only if the Riemann Hypothesis holds. -/

/-- The index set: the nontrivial zeros of `ζ`. -/
abbrev ZeroIdx : Type := {s : ℂ // IsNontrivialZero s}

instance : DecidableEq ZeroIdx := Classical.decEq _

/-- The standard unit vector of `ℓ²(ZeroIdx, ℂ)` attached to a nontrivial zero. -/
def zeroBasisVec (i : ZeroIdx) : lp (fun _ : ZeroIdx => ℂ) 2 := lp.single 2 i (1 : ℂ)

lemma orthonormal_zeroBasisVec : Orthonormal ℂ zeroBasisVec := by
  constructor
  · intro i
    simp [zeroBasisVec, lp.norm_single]
  · intro i j hij
    simp [zeroBasisVec, lp.inner_single_left, lp.single_apply, hij]

/-- The algebraic span of the standard unit vectors indexed by the nontrivial zeros; a
complex inner product space (not complete, which is irrelevant here). -/
def BrockianSpace : Submodule ℂ (lp (fun _ : ZeroIdx => ℂ) 2) :=
  Submodule.span ℂ (Set.range zeroBasisVec)

/-- The canonical basis of `BrockianSpace`, indexed by the nontrivial zeros. -/
def brockianBasis : Module.Basis ZeroIdx ℂ BrockianSpace :=
  Module.Basis.span orthonormal_zeroBasisVec.linearIndependent

lemma coe_brockianBasis (i : ZeroIdx) :
    ((brockianBasis i : BrockianSpace) : lp (fun _ : ZeroIdx => ℂ) 2) = zeroBasisVec i :=
  Module.Basis.span_apply _ i

lemma inner_brockianBasis (i j : ZeroIdx) :
    (inner ℂ (brockianBasis i) (brockianBasis j) : ℂ) = if i = j then 1 else 0 := by
  rw [Submodule.coe_inner, coe_brockianBasis, coe_brockianBasis]
  by_cases h : i = j
  · subst h; simp [zeroBasisVec]
  · simp [h, zeroBasisVec, lp.inner_single_left, lp.single_apply]

/-- The spectral parameter attached to a nontrivial zero. -/
def spectralParam (i : ZeroIdx) : ℂ := -Complex.I * ((i : ℂ) - 1 / 2)

/-- The diagonal operator on `BrockianSpace` whose eigenvalue at the basis vector indexed by
a nontrivial zero `s` is the spectral parameter `-i (s - 1/2)`. -/
def brockianOp : BrockianSpace →ₗ[ℂ] BrockianSpace :=
  (brockianBasis.constr ℂ) fun i => spectralParam i • brockianBasis i

lemma brockianOp_basis (i : ZeroIdx) :
    brockianOp (brockianBasis i) = spectralParam i • brockianBasis i := by
  simp [brockianOp, Module.Basis.constr_basis]

lemma conj_spectralParam (hRH : RiemannHypothesis) (i : ZeroIdx) :
    conj (spectralParam i) = spectralParam i := by
  refine Complex.conj_eq_iff_im.mpr ?_
  have hre : (i : ℂ).re = 1 / 2 := hRH i.1 i.2
  simp [spectralParam, hre]

lemma brockianOp_symm_basis_left (hRH : RiemannHypothesis) (i : ZeroIdx)
    (y : BrockianSpace) :
    (inner ℂ (brockianOp (brockianBasis i)) y : ℂ)
      = inner ℂ (brockianBasis i) (brockianOp y) := by
  have key : ((innerSL ℂ (brockianOp (brockianBasis i))).toLinearMap : BrockianSpace →ₗ[ℂ] ℂ)
      = ((innerSL ℂ (brockianBasis i)).toLinearMap : BrockianSpace →ₗ[ℂ] ℂ) ∘ₗ brockianOp := by
    refine brockianBasis.ext ?_
    intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply, brockianOp_basis, inner_smul_left, inner_smul_right,
      inner_brockianBasis, conj_spectralParam hRH]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simpa using congrArg (fun f => f y) key

lemma brockianOp_symm (hRH : RiemannHypothesis) (x y : BrockianSpace) :
    (inner ℂ (brockianOp x) y : ℂ) = inner ℂ x (brockianOp y) := by
  have key : ((innerSL ℂ y).toLinearMap : BrockianSpace →ₗ[ℂ] ℂ) ∘ₗ brockianOp
      = ((innerSL ℂ (brockianOp y)).toLinearMap : BrockianSpace →ₗ[ℂ] ℂ) := by
    refine brockianBasis.ext ?_
    intro i
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    rw [← inner_conj_symm y (brockianOp (brockianBasis i)),
      brockianOp_symm_basis_left hRH i y, inner_conj_symm]
  have hxy := congrArg (fun f => f x) key
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply] at hxy
  rw [← inner_conj_symm (brockianOp x) y, hxy, inner_conj_symm]

/-- **Converse construction.** If the Riemann Hypothesis holds, then `BrockianSpace` carries
a Brockian system: the diagonal operator with the (then real) spectral parameters as
eigenvalues is symmetric, and each basis vector is a nonzero eigenvector. -/
def brockianSystemOfRH (hRH : RiemannHypothesis) : BrockianSystem BrockianSpace where
  T := brockianOp
  selfAdjoint := brockianOp_symm hRH
  spectral := by
    intro s hs
    refine ⟨brockianBasis ⟨s, hs⟩, brockianBasis.ne_zero _, ?_⟩
    simpa [spectralParam] using brockianOp_basis ⟨s, hs⟩

/-- **The hypothesis of `RH_of_BrockianSystem` is exactly the Riemann Hypothesis.**
A Brockian system exists on the canonical space `BrockianSpace` if and only if every
nontrivial zero of `ζ` lies on the critical line. In particular the hypothesis is neither
vacuous nor contradictory: it is equivalent to RH, and hence remains open. -/
theorem nonempty_brockianSystem_iff_RH :
    Nonempty (BrockianSystem BrockianSpace) ↔ RiemannHypothesis :=
  ⟨fun ⟨B⟩ => RH_of_BrockianSystem B, fun hRH => ⟨brockianSystemOfRH hRH⟩⟩

end RiemannScaffold
end Brockian

