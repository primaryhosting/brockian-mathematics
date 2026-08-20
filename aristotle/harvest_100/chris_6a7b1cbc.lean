import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

/-! ## The abstract twist argument

The Lieb–Schultz–Mattis theorem states that a translation invariant spin chain with
half-integer spin per site cannot have a unique ground state separated by a spectral gap:
it is either gapless (in the thermodynamic limit) or has a degenerate ground state.

The mechanism, discovered by Lieb, Schultz and Mattis, is the *twist* (or *large gauge
transformation*) operator `U = exp (2πi/L ∑ j Sᶻⱼ)`.  Applied to the ground state it
produces a variational state whose energy exceeds the ground state energy by `O(1/L)`,
and whose momentum is shifted by exactly `π` relative to the ground state precisely
because the spin per site is half-integer.  The momentum shift forces the twisted state
to be orthogonal to the ground state, so it is a genuine low lying excitation.

`Phys.lieb_schultz_mattis` below is the general form of this argument in an arbitrary
complex inner product space: `T` is the (isometric) translation operator, `psi` a
ground state of momentum `c`, `U` the twist operator, and the hypothesis `hshift`
records the half-integer-spin momentum shift `T (U psi) = -c • (U psi)`.  The
conclusion says that the spectral gap above `psi` is at most `eps`: there is a unit
state orthogonal to `psi` whose energy is within `eps` of the ground state energy
(degeneracy when `eps = 0`, gaplessness in the thermodynamic limit when `eps = O(1/L)`).

In `Phys.SpinChain` the momentum shift hypothesis is *derived* for the concrete
spin-`1/2` chain of `L` sites in the zero magnetization sector, see
`Phys.SpinChain.trans_twist_anticomm` and
`Phys.SpinChain.lieb_schultz_mattis_spin_half_chain`.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The energy expectation value `⟪x, A x⟫` of a state `x` for the Hamiltonian `A`. -/
noncomputable def energy (A : V →L[ℂ] V) (x : V) : ℝ := (⟪x, A x⟫_ℂ).re

/-- **Lieb–Schultz–Mattis theorem** (twist-operator form).

Let `T` be an isometric translation operator, `psi` a normalised ground state which is a
translation eigenvector of eigenvalue `c` (a momentum eigenstate), and `U` a twist
operator which produces a normalised state `U psi` whose momentum is shifted by `π`
(`T (U psi) = -(c • U psi)`; this shift is exactly what half-integer spin per site
produces, cf. `Phys.SpinChain.trans_twist_anticomm`) and whose energy exceeds that of
`psi` by at most `eps`.

Then the system is gapless or degenerate: there is a unit state orthogonal to the ground
state `psi` whose energy is at most `energy A psi + eps`. -/
theorem lieb_schultz_mattis
    (A T U : V →L[ℂ] V)
    (hT : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (psi : V) (hpsi : ‖psi‖ = 1)
    (c : ℂ) (hTpsi : T psi = c • psi)
    (hshift : T (U psi) = -(c • U psi))
    (hUnorm : ‖U psi‖ = 1)
    (eps : ℝ)
    (hvar : energy A (U psi) ≤ energy A psi + eps) :
    ∃ phi : V, ‖phi‖ = 1 ∧ ⟪psi, phi⟫_ℂ = 0 ∧ energy A phi ≤ energy A psi + eps := by
  refine ⟨U psi, hUnorm, ?_, hvar⟩
  have hc : (starRingEnd ℂ) c * c = 1 := by
    have h1 : ⟪T psi, T psi⟫_ℂ = ⟪psi, psi⟫_ℂ := hT psi psi
    rw [hTpsi, inner_smul_left, inner_smul_right] at h1
    have h2 : ⟪psi, psi⟫_ℂ = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hpsi]
    rw [h2] at h1
    simpa using h1
  have key : ⟪psi, U psi⟫_ℂ = -⟪psi, U psi⟫_ℂ := by
    have h1 : ⟪T psi, T (U psi)⟫_ℂ = ⟪psi, U psi⟫_ℂ := hT psi (U psi)
    rw [hTpsi, hshift, inner_neg_right, inner_smul_left, inner_smul_right,
      ← mul_assoc, hc, one_mul] at h1
    exact h1.symm
  linear_combination key / 2

/-! ## Operators on a finite configuration space -/

namespace Op

variable {ι : Type*} [Fintype ι]

/-- The diagonal (multiplication) operator with symbol `w` on `EuclideanSpace ℂ ι`. -/
noncomputable def diagOp (w : ι → ℂ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun psi => WithLp.toLp 2 (fun s => w s * psi s)
      map_add' := by intro x y; ext s; simp [mul_add]
      map_smul' := by intro c x; ext s; simp [mul_left_comm] }

@[simp] lemma diagOp_apply (w : ι → ℂ) (psi : EuclideanSpace ℂ ι) (s : ι) :
    diagOp w psi s = w s * psi s := by simp [diagOp]

/-- The operator induced by a relabelling `e` of the configurations. -/
noncomputable def permOp (e : ι → ι) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun psi => WithLp.toLp 2 (fun s => psi (e s))
      map_add' := by intro x y; ext s; simp
      map_smul' := by intro c x; ext s; simp }

@[simp] lemma permOp_apply (e : ι → ι) (psi : EuclideanSpace ℂ ι) (s : ι) :
    permOp e psi s = psi (e s) := by simp [permOp]

/-- A relabelling operator is an isometry (it is a permutation unitary). -/
lemma permOp_inner (e : ι ≃ ι) (x y : EuclideanSpace ℂ ι) :
    ⟪permOp (e : ι → ι) x, permOp (e : ι → ι) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, permOp_apply]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- A diagonal operator with unimodular symbol preserves norms. -/
lemma norm_diagOp (w : ι → ℂ) (hw : ∀ s, ‖w s‖ = 1) (x : EuclideanSpace ℂ ι) :
    ‖diagOp w x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, diagOp_apply, norm_mul, hw, one_mul]

end Op

/-! ## The spin-`1/2` chain: derivation of the momentum shift -/

namespace SpinChain

open Op

/-- A configuration of the chain of `L` sites: each site carries a spin-`1/2`
pointing up (`true`) or down (`false`). -/
abbrev SpinConfig (L : ℕ) := Fin L → Bool

/-- Twice the `z`-component of the spin at a site; it is *odd* (`±1`), which is
exactly the statement that the spin per site is half-integer. -/
def twoSz (b : Bool) : ℤ := if b then 1 else -1

lemma twoSz_eq_one_or (b : Bool) : twoSz b = 1 ∨ twoSz b = -1 := by
  cases b <;> simp [twoSz]

/-- Translation of a configuration by one site. -/
def shift {n : ℕ} (s : SpinConfig (n + 1)) : SpinConfig (n + 1) := fun j => s (j + 1)

/-- Translation of configurations, as an equivalence. -/
def shiftEquiv (n : ℕ) : SpinConfig (n + 1) ≃ SpinConfig (n + 1) where
  toFun := shift
  invFun := fun s j => s (j - 1)
  left_inv := by intro s; funext j; simp [shift]
  right_inv := by intro s; funext j; simp [shift]

@[simp] lemma shiftEquiv_apply {n : ℕ} (s : SpinConfig (n + 1)) :
    shiftEquiv n s = shift s := rfl

/-- Twice the total magnetisation `∑ⱼ Sᶻⱼ` of a configuration. -/
def mag {L : ℕ} (s : SpinConfig L) : ℤ := ∑ j, twoSz (s j)

/-- Twice the weighted magnetisation `∑ⱼ j Sᶻⱼ`, the generator of the twist. -/
def wmag {L : ℕ} (s : SpinConfig L) : ℤ := ∑ j, (j.val : ℤ) * twoSz (s j)

lemma mag_shift {n : ℕ} (s : SpinConfig (n + 1)) : mag (shift s) = mag s :=
  Fintype.sum_equiv (Equiv.addRight (1 : Fin (n + 1))) _ _ (fun _ => rfl)

/-- The key index computation behind the momentum shift: translating a configuration
changes the twist generator by `-mag s + L * (2 Sᶻ₀)`. -/
lemma wmag_shift {n : ℕ} (s : SpinConfig (n + 1)) :
    wmag (shift s) = wmag s - mag s + (n + 1) * twoSz (s 0) := by
  simp only [wmag, mag, shift]
  rw [Fin.sum_univ_castSucc (f := fun j : Fin (n + 1) => (j.val : ℤ) * twoSz (s (j + 1))),
    Fin.sum_univ_succ (f := fun k : Fin (n + 1) => (k.val : ℤ) * twoSz (s k)),
    Fin.sum_univ_succ (f := fun k : Fin (n + 1) => twoSz (s k))]
  have h2 : (Fin.last n : Fin (n + 1)) + 1 = 0 := by simp
  simp only [Fin.coeSucc_eq_succ, h2, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_zero,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
  ring

/-- The phase `2π/L * ∑ⱼ j Sᶻⱼ = π/L * ∑ⱼ j (2Sᶻⱼ)` of the twist operator. -/
noncomputable def twistAngle (n : ℕ) (s : SpinConfig (n + 1)) : ℝ :=
  Real.pi * (wmag s : ℝ) / (n + 1)

/-- The symbol of the twist (large gauge transformation) operator
`U = exp (2πi/L ∑ⱼ j Sᶻⱼ)`. -/
noncomputable def twistPhase (n : ℕ) (s : SpinConfig (n + 1)) : ℂ :=
  Complex.exp (twistAngle n s * Complex.I)

lemma norm_twistPhase (n : ℕ) (s : SpinConfig (n + 1)) : ‖twistPhase n s‖ = 1 := by
  simp [twistPhase, Complex.norm_exp]

lemma twistAngle_shift {n : ℕ} (s : SpinConfig (n + 1)) (hs : mag s = 0) :
    twistAngle n (shift s) = twistAngle n s + Real.pi * (twoSz (s 0) : ℝ) := by
  have hL : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [twistAngle, wmag_shift, hs]
  push_cast
  field_simp
  ring

/-- **The half-integer-spin momentum shift.**  In the zero magnetisation sector the
twist phase is *anti*-periodic under translation: `w (shift s) = - w s`.  The sign is
`exp (2πi Sᶻ₀) = -1`, which holds precisely because the spin per site is half-integer
(`twoSz` is odd). -/
lemma twistPhase_shift {n : ℕ} (s : SpinConfig (n + 1)) (hs : mag s = 0) :
    twistPhase n (shift s) = -twistPhase n s := by
  have h := twistAngle_shift s hs
  simp only [twistPhase, h]
  push_cast
  rw [add_mul, Complex.exp_add]
  rcases twoSz_eq_one_or (s 0) with h1 | h1 <;> rw [h1]
  · push_cast
    rw [mul_one, Complex.exp_pi_mul_I]
    ring
  · push_cast
    rw [show (Real.pi : ℂ) * -1 * Complex.I = -((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    field_simp

/-- The Hilbert space of the spin-`1/2` chain with `n + 1` sites: it has the
configuration basis as an orthonormal basis. -/
abbrev ChainSpace (n : ℕ) := EuclideanSpace ℂ (SpinConfig (n + 1))

/-- The translation (one-site shift) operator on the chain. -/
noncomputable def transOp (n : ℕ) : ChainSpace n →L[ℂ] ChainSpace n :=
  permOp (shift : SpinConfig (n + 1) → SpinConfig (n + 1))

/-- The Lieb–Schultz–Mattis twist operator `U = exp (2πi/L ∑ⱼ j Sᶻⱼ)`. -/
noncomputable def twistOp (n : ℕ) : ChainSpace n →L[ℂ] ChainSpace n :=
  diagOp (twistPhase n)

lemma transOp_inner (n : ℕ) (x y : ChainSpace n) :
    ⟪transOp n x, transOp n y⟫_ℂ = ⟪x, y⟫_ℂ :=
  permOp_inner (shiftEquiv n) x y

lemma norm_twistOp (n : ℕ) (x : ChainSpace n) : ‖twistOp n x‖ = ‖x‖ :=
  norm_diagOp _ (norm_twistPhase n) x

/-- **Translation and twist anticommute on the zero magnetisation sector.**

This is the algebraic heart of the Lieb–Schultz–Mattis argument: since each site carries
half-integer spin, `exp (2πi Sᶻⱼ) = -1`, so conjugating the twist by the translation
produces the extra sign `-1`.  Consequently the twisted state carries momentum shifted by
`π` relative to the state it is built from. -/
theorem trans_twist_anticomm (n : ℕ) (psi : ChainSpace n)
    (hpsi : ∀ s, mag s ≠ 0 → psi s = 0) :
    transOp n (twistOp n psi) = -(twistOp n (transOp n psi)) := by
  ext s
  by_cases h : mag s = 0
  · simp only [transOp, twistOp, permOp_apply, diagOp_apply, PiLp.neg_apply]
    rw [twistPhase_shift s h]
    ring
  · have h1 : psi (shift s) = 0 := hpsi _ (by rwa [mag_shift])
    simp only [transOp, twistOp, permOp_apply, diagOp_apply, PiLp.neg_apply, h1]
    ring

/-- **Lieb–Schultz–Mattis for the spin-`1/2` chain.**

Let `psi` be a normalised ground state of a spin-`1/2` chain with `n + 1` sites lying in
the zero magnetisation sector, which is an eigenvector of the translation operator
(a momentum eigenstate, as is always possible for a translation invariant Hamiltonian).
If the Lieb–Schultz–Mattis twisted state `twistOp n psi` has energy at most
`energy A psi + eps` (the standard variational estimate gives `eps = O(1/n)`), then the
chain is gapless or degenerate: there is a unit state *orthogonal* to `psi` with energy
at most `energy A psi + eps`.

Note that the orthogonality — the nontrivial content — is not assumed: it follows from
the `π` momentum shift produced by the half-integer spin, via
`trans_twist_anticomm`. -/
theorem lieb_schultz_mattis_spin_half_chain (n : ℕ) (A : ChainSpace n →L[ℂ] ChainSpace n)
    (psi : ChainSpace n) (hpsi : ‖psi‖ = 1)
    (hsector : ∀ s, mag s ≠ 0 → psi s = 0)
    (c : ℂ) (hmom : transOp n psi = c • psi)
    (eps : ℝ) (hvar : energy A (twistOp n psi) ≤ energy A psi + eps) :
    ∃ phi : ChainSpace n, ‖phi‖ = 1 ∧ ⟪psi, phi⟫_ℂ = 0 ∧
      energy A phi ≤ energy A psi + eps := by
  refine lieb_schultz_mattis A (transOp n) (twistOp n) (transOp_inner n) psi hpsi c hmom ?_ ?_
    eps hvar
  · rw [trans_twist_anticomm n psi hsector, hmom, map_smul]
  · rw [norm_twistOp, hpsi]

end SpinChain

/-! ## Non-vacuity

A two-level realisation of the hypotheses of `Phys.lieb_schultz_mattis`
(the Pauli matrices `X` and `Z`, which anticommute, in the role of translation and
twist), showing that the hypothesis set is consistent and the theorem is not vacuous. -/

section NonVacuous

open Op

private noncomputable def pauliX : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  permOp (fun i => Equiv.swap 0 1 i)

private noncomputable def pauliZ : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  diagOp (fun i => if i = 0 then 1 else -1)

private noncomputable def plusState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun _ => ((Real.sqrt 2)⁻¹ : ℝ))

theorem lieb_schultz_mattis_hypotheses_nonvacuous :
    ∃ (A T U : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
      (psi : EuclideanSpace ℂ (Fin 2)) (c : ℂ) (eps : ℝ),
      (∀ x y, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ ‖psi‖ = 1 ∧ T psi = c • psi ∧
      T (U psi) = -(c • U psi) ∧ ‖U psi‖ = 1 ∧
      energy A (U psi) ≤ energy A psi + eps ∧ U psi ≠ psi := by
  have hpos : (0 : ℝ) < ((Real.sqrt 2)⁻¹ : ℝ) := by positivity
  have hval : ∀ i, plusState i = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := fun _ => rfl
  have hnorm : ‖plusState‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [hval, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hpos.le]
    rw [show ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 + ((Real.sqrt 2)⁻¹ : ℝ) ^ 2
        = ((Real.sqrt 2) ^ 2)⁻¹ * 2 by ring, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨0, pauliX, pauliZ, plusState, 1, 0, ?_, hnorm, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y => permOp_inner (Equiv.swap 0 1) x y
  · ext i
    simp [pauliX, hval]
  · ext i
    fin_cases i <;> simp [pauliX, pauliZ, hval]
  · rw [pauliZ, norm_diagOp _ (fun i => by by_cases h : i = 0 <;> simp [h]), hnorm]
  · simp [energy]
  · intro h
    have h1 : pauliZ plusState 1 = plusState 1 := by rw [h]
    simp only [pauliZ, diagOp_apply, hval] at h1
    norm_num at h1
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 0 := by linear_combination -h1 / 2
    rw [inv_eq_zero, Complex.ofReal_eq_zero] at h2
    rw [h2] at hpos
    simp at hpos

end NonVacuous

end Phys

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

