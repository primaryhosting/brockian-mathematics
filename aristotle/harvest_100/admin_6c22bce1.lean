/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
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

/-!
## Setting

We formalise the Lieb–Schultz–Mattis (LSM) theorem in its finite-volume, variational form
(Lieb–Schultz–Mattis 1961, Affleck–Lieb 1986, Oshikawa 2000).

For each system size `L` we have a finite dimensional complex Hilbert space `E L`
(the state space of a chain of `L` sites), a self-adjoint Hamiltonian `Ham L`, and a
unitary translation operator `Tr L`.  The two physical inputs of LSM are:

* the ground state `ψ₀ L` is a translation eigenstate, `Tr L ψ₀ = ω • ψ₀` with `‖ω‖ = 1`
  (its momentum);
* for a chain with **half-integer spin per unit cell** the Lieb–Schultz–Mattis twist
  `ψ₁ L = U_twist ψ₀ L` is a normalised state whose momentum is shifted by exactly `π`,
  i.e. `Tr L ψ₁ = (-ω) • ψ₁`, and whose energy exceeds the ground energy by at most
  `C / L` (the twist is a low-energy variational state).

The theorem proved below is that these inputs are incompatible with the chain having,
for every size, a *unique* ground state separated from the rest of the spectrum by a
gap `γ > 0` that does not shrink with `L`.  In other words the chain is gapless or its
ground state is degenerate.
-/

namespace Phys

open Module

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The energy (expectation value of the Hamiltonian `H`) of a state `ψ`. -/
noncomputable def energy (H : E →ₗ[ℂ] E) (ψ : E) : ℝ := (inner ℂ ψ (H ψ)).re

/-- `GappedGroundState H ψ₀ E₀ γ` says that the self-adjoint Hamiltonian `H` has `ψ₀` as a
normalised ground state of energy `E₀`, that this ground state is *unique* (the `E₀`
eigenspace is the line spanned by `ψ₀`, i.e. no degeneracy), and that every other
eigenvalue of `H` is at least `E₀ + γ` (a spectral gap of size `γ`). -/
structure GappedGroundState (H : E →ₗ[ℂ] E) (ψ₀ : E) (E₀ γ : ℝ) : Prop where
  /-- The Hamiltonian is self-adjoint. -/
  isSymmetric : H.IsSymmetric
  /-- The ground state is normalised. -/
  norm_ground : ‖ψ₀‖ = 1
  /-- `ψ₀` is an eigenvector of energy `E₀`. -/
  ham_ground : H ψ₀ = (E₀ : ℂ) • ψ₀
  /-- The ground state is non-degenerate. -/
  simple : ∀ v : E, H v = (E₀ : ℂ) • v → ∃ c : ℂ, v = c • ψ₀
  /-- Every eigenvalue is either the ground energy or at least `E₀ + γ`. -/
  spectral_gap : ∀ (μ : ℝ) (v : E), v ≠ 0 → H v = (μ : ℂ) • v → μ = E₀ ∨ E₀ + γ ≤ μ

omit [FiniteDimensional ℂ E] in
/-- Parseval's identity in an orthonormal basis. -/
theorem norm_sq_eq_sum_inner_sq {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) :
    ‖ψ‖ ^ 2 = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  have h := b.sum_inner_mul_inner ψ ψ
  have key : ∀ i : Fin n, inner ℂ ψ (b i) * inner ℂ (b i) ψ = ((‖inner ℂ (b i) ψ‖ : ℂ)) ^ 2 := by
    intro i
    rw [(inner_conj_symm ψ (b i)).symm]
    exact RCLike.conj_mul _
  have h2 : (∑ i, ((‖inner ℂ (b i) ψ‖ : ℂ)) ^ 2) = (‖ψ‖ ^ 2 : ℂ) := by
    rw [← Finset.sum_congr rfl (fun i _ => key i), h, inner_self_eq_norm_sq_to_K]
    norm_num
  exact_mod_cast h2.symm

/-- The energy of a state, expanded in an eigenbasis of the self-adjoint Hamiltonian:
`⟪ψ, H ψ⟫ = ∑ᵢ μᵢ |⟪bᵢ, ψ⟫|²`. -/
theorem energy_eq_sum_eigenvalues {H : E →ₗ[ℂ] E} (hT : H.IsSymmetric) {n : ℕ}
    (hn : finrank ℂ E = n) (ψ : E) :
    energy H ψ = ∑ i, hT.eigenvalues hn i * ‖inner ℂ (hT.eigenvectorBasis hn i) ψ‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn with hb
  have h := b.sum_inner_mul_inner ψ (H ψ)
  have key : ∀ i : Fin n, inner ℂ ψ (b i) * inner ℂ (b i) (H ψ)
      = ((hT.eigenvalues hn i : ℂ)) * ((‖inner ℂ (b i) ψ‖ : ℂ)) ^ 2 := by
    intro i
    have e1 : inner ℂ (b i) (H ψ) = ((hT.eigenvalues hn i : ℂ)) * inner ℂ (b i) ψ := by
      rw [← hT (b i) ψ, hT.apply_eigenvectorBasis hn i, ← hb, inner_smul_left]
      simp
    have e2 : inner ℂ ψ (b i) = (starRingEnd ℂ) (inner ℂ (b i) ψ) := (inner_conj_symm ψ (b i)).symm
    have e3 : (starRingEnd ℂ) (inner ℂ (b i) ψ) * inner ℂ (b i) ψ
        = ((‖inner ℂ (b i) ψ‖ : ℂ)) ^ 2 := RCLike.conj_mul _
    rw [e1, e2]
    linear_combination ((hT.eigenvalues hn i : ℂ)) * e3
  have h3 : (∑ i, inner ℂ ψ (b i) * inner ℂ (b i) (H ψ))
      = ((∑ i, hT.eigenvalues hn i * ‖inner ℂ (b i) ψ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun i _ => key i)
  rw [energy, ← h, h3, Complex.ofReal_re]

/-- **Variational form of the spectral gap.**  If `H` has a unique ground state `ψ₀` of energy
`E₀` and a spectral gap `γ`, then every state orthogonal to `ψ₀` has energy at least
`(E₀ + γ) ‖ψ‖²`.  This is the Courant–Fischer / Rayleigh-quotient input to LSM. -/
theorem GappedGroundState.energy_ge_of_orthogonal {H : E →ₗ[ℂ] E} {ψ₀ : E} {E₀ γ : ℝ}
    (h : GappedGroundState H ψ₀ E₀ γ) {ψ : E} (horth : inner ℂ ψ₀ ψ = 0) :
    (E₀ + γ) * ‖ψ‖ ^ 2 ≤ energy H ψ := by
  obtain ⟨hsym, _, _, hsimple, hgap⟩ := h
  have hn : finrank ℂ E = finrank ℂ E := rfl
  have hcoef : ∀ i, inner ℂ (hsym.eigenvectorBasis hn i) ψ ≠ 0 → E₀ + γ ≤ hsym.eigenvalues hn i := by
    intro i hne
    have hbnorm : ‖hsym.eigenvectorBasis hn i‖ = 1 := (hsym.eigenvectorBasis hn).orthonormal.1 i
    have hbne : hsym.eigenvectorBasis hn i ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hbnorm
      norm_num at hbnorm
    rcases hgap _ _ hbne (hsym.apply_eigenvectorBasis hn i) with heq | hle
    · exfalso
      apply hne
      have heq' : hsym.eigenvalues hn i = E₀ := by simpa using heq
      obtain ⟨c, hc⟩ := hsimple (hsym.eigenvectorBasis hn i)
        (by rw [hsym.apply_eigenvectorBasis hn i, heq']; rfl)
      rw [hc, inner_smul_left, horth, mul_zero]
    · exact hle
  rw [energy_eq_sum_eigenvalues hsym hn ψ,
    norm_sq_eq_sum_inner_sq (hsym.eigenvectorBasis hn) ψ, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  by_cases hc : inner ℂ (hsym.eigenvectorBasis hn i) ψ = 0
  · simp [hc]
  · exact mul_le_mul_of_nonneg_right (hcoef i hc) (sq_nonneg _)

omit [FiniteDimensional ℂ E] in
/-- **Momentum-`π` orthogonality.**  Two eigenstates of a unitary (here: the translation
operator) whose eigenvalues differ by a sign are orthogonal.  For a half-integer-spin chain
the Lieb–Schultz–Mattis twist shifts the momentum by exactly `π`, so the twisted state is
orthogonal to the ground state. -/
theorem inner_eq_zero_of_momentum_shift {U : E ≃ₗᵢ[ℂ] E} {ω : ℂ} {ψ₀ ψ₁ : E}
    (hω : ‖ω‖ = 1) (h0 : U ψ₀ = ω • ψ₀) (h1 : U ψ₁ = (-ω) • ψ₁) :
    inner ℂ ψ₀ ψ₁ = 0 := by
  have hmap : inner ℂ (U ψ₀) (U ψ₁) = inner ℂ ψ₀ ψ₁ := U.inner_map_map ψ₀ ψ₁
  rw [h0, h1, inner_smul_left, inner_smul_right] at hmap
  have hconj : (starRingEnd ℂ) ω * ω = 1 := by
    rw [RCLike.conj_mul, hω]
    norm_num
  have h2 : (2 : ℂ) * inner ℂ ψ₀ ψ₁ = 0 := by
    have : (starRingEnd ℂ) ω * (-ω * inner ℂ ψ₀ ψ₁) = inner ℂ ψ₀ ψ₁ := hmap
    linear_combination -this - inner ℂ ψ₀ ψ₁ * hconj
  simpa using h2

/-- **Finite-volume Lieb–Schultz–Mattis bound.**  If at system size `L` the chain has a unique
ground state `ψ₀` with energy `E₀` and spectral gap `γ`, and the twisted state `ψ₁` is a
normalised state with translation eigenvalue `-w` (momentum shifted by `π` relative to the
ground state) and energy at most `E₀ + ε`, then `γ ≤ ε`. -/
theorem gap_le_of_twisted_state {H : E →ₗ[ℂ] E} {U : E ≃ₗᵢ[ℂ] E} {ψ₀ ψ₁ : E}
    {E₀ γ ε : ℝ} {w : ℂ} (hw : ‖w‖ = 1)
    (h : GappedGroundState H ψ₀ E₀ γ)
    (h0 : U ψ₀ = w • ψ₀) (h1 : U ψ₁ = (-w) • ψ₁) (hnorm : ‖ψ₁‖ = 1)
    (hvar : energy H ψ₁ ≤ E₀ + ε) : γ ≤ ε := by
  have horth : inner ℂ ψ₀ ψ₁ = 0 := inner_eq_zero_of_momentum_shift hw h0 h1
  have hge : (E₀ + γ) * ‖ψ₁‖ ^ 2 ≤ energy H ψ₁ := h.energy_ge_of_orthogonal horth
  rw [hnorm] at hge
  simp only [one_pow, mul_one] at hge
  linarith

end Spectral

section LSM

variable {E : ℕ → Type*} [∀ L, NormedAddCommGroup (E L)] [∀ L, InnerProductSpace ℂ (E L)]
  [∀ L, FiniteDimensional ℂ (E L)]

/-- **Lieb–Schultz–Mattis theorem** (finite-volume variational form).

A translation-invariant chain with half-integer spin per unit cell is gapless or has a
degenerate ground state.

Hypotheses (for every system size `L`):
* `Tr L` is a unitary translation operator;
* the ground state `ψ₀ L` has translation eigenvalue `ω L` of modulus one;
* **half-integer spin**: the Lieb–Schultz–Mattis twisted state `ψ₁ L` is normalised, has
  translation eigenvalue `-(ω L)` (momentum shifted by `π`) and energy at most `E₀ L + C / L`.

Conclusion: there is *no* `γ > 0` such that at every system size the chain has a unique
ground state `ψ₀ L` of energy `E₀ L` with spectral gap `γ`.  Equivalently: either the gap
closes as `L → ∞` (gapless), or for some sizes the ground state is degenerate. -/
theorem lieb_schultz_mattis
    (Ham : ∀ L, E L →ₗ[ℂ] E L) (Tr : ∀ L, E L ≃ₗᵢ[ℂ] E L)
    (ψ₀ ψ₁ : ∀ L, E L) (E₀ : ℕ → ℝ) (ω : ℕ → ℂ) (C : ℝ)
    (hω : ∀ L, ‖ω L‖ = 1)
    (htrans₀ : ∀ L, Tr L (ψ₀ L) = ω L • ψ₀ L)
    (htrans₁ : ∀ L, Tr L (ψ₁ L) = (-(ω L)) • ψ₁ L)
    (hnorm₁ : ∀ L, ‖ψ₁ L‖ = 1)
    (hvar : ∀ L, 0 < L → energy (Ham L) (ψ₁ L) ≤ E₀ L + C / L) :
    ¬ ∃ γ : ℝ, 0 < γ ∧ ∀ L, 0 < L → GappedGroundState (Ham L) (ψ₀ L) (E₀ L) γ := by
  rintro ⟨γ, hγ, hgapped⟩
  -- pick a system size `L` so large that the twist energy `C / L` is below the gap `γ`
  set L : ℕ := ⌈C / γ⌉₊ + 1 with hL
  have hLpos : 0 < L := Nat.succ_pos _
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hCL : C / (L : ℝ) < γ := by
    have h1 : C / γ ≤ (⌈C / γ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : C / γ < (L : ℝ) := by
      rw [hL]
      push_cast
      linarith
    have h3 : C < γ * (L : ℝ) := by
      have := (div_lt_iff₀ hγ).mp h2
      linarith
    exact (div_lt_iff₀ hLreal).mpr (by linarith)
  -- the twisted state is orthogonal to the ground state and has energy within `C / L`
  have hle : γ ≤ C / (L : ℝ) :=
    gap_le_of_twisted_state (hω L) (hgapped L hLpos)
      (htrans₀ L) (htrans₁ L) (hnorm₁ L) (hvar L hLpos)
  linarith

/-- The `π`-momentum-shift reflection on a two-site toy state space: it fixes the first
basis vector and negates the second.  Used only to certify that the hypotheses of
`lieb_schultz_mattis` are satisfiable. -/
noncomputable def toyShift : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = 0 then LinearIsometryEquiv.refl ℂ ℂ else LinearIsometryEquiv.neg ℂ)

/-- **Non-vacuity.**  The hypotheses of `lieb_schultz_mattis` are satisfiable, so the theorem
is not vacuously true. -/
theorem lieb_schultz_mattis_hypotheses_satisfiable :
    ∃ (Ham : ∀ _L : ℕ, EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (Tr : ∀ _L : ℕ, EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2))
      (ψ₀ ψ₁ : ∀ _L : ℕ, EuclideanSpace ℂ (Fin 2)) (E₀ : ℕ → ℝ) (ω : ℕ → ℂ) (C : ℝ),
      (∀ L, ‖ω L‖ = 1) ∧ (∀ L, Tr L (ψ₀ L) = ω L • ψ₀ L) ∧
        (∀ L, Tr L (ψ₁ L) = (-(ω L)) • ψ₁ L) ∧ (∀ L, ‖ψ₁ L‖ = 1) ∧
        (∀ L, 0 < L → energy (Ham L) (ψ₁ L) ≤ E₀ L + C / L) := by
  refine ⟨fun _ => 0, fun _ => toyShift, fun _ => EuclideanSpace.single 0 1,
    fun _ => EuclideanSpace.single 1 1, fun _ => 0, fun _ => 1, 0, fun L => by simp, ?_, ?_, ?_, ?_⟩
  · intro L
    ext i
    fin_cases i <;>
      simp [toyShift, LinearIsometryEquiv.piLpCongrRight_apply, EuclideanSpace.single_apply]
  · intro L
    ext i
    fin_cases i <;>
      simp [toyShift, LinearIsometryEquiv.piLpCongrRight_apply, EuclideanSpace.single_apply]
  · intro L
    simp
  · intro L _
    simp [energy]

/-- A two-level toy Hamiltonian: it annihilates the first basis vector and acts as the
identity on the second.  Used only to certify that `GappedGroundState` is satisfiable. -/
noncomputable def toyHam : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun x := EuclideanSpace.single 1 (x 1)
  map_add' x y := by ext i; fin_cases i <;> simp [EuclideanSpace.single_apply]
  map_smul' c x := by ext i; fin_cases i <;> simp [EuclideanSpace.single_apply]

/-- **Non-vacuity of the conclusion.**  `GappedGroundState` is satisfiable: the toy
Hamiltonian has the unique ground state `e₀` of energy `0` and spectral gap `1`. -/
theorem gappedGroundState_toy :
    GappedGroundState toyHam (EuclideanSpace.single 0 (1 : ℂ)) 0 1 where
  isSymmetric := by
    intro x y
    simp [toyHam, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, mul_comm]
  norm_ground := by simp
  ham_ground := by
    ext i
    fin_cases i <;> simp [toyHam, EuclideanSpace.single_apply]
  simple := by
    intro v hv
    refine ⟨v.ofLp 0, ?_⟩
    have h1 : v.ofLp 1 = 0 := by
      have := congrFun (congrArg WithLp.ofLp hv) 1
      simpa [toyHam, EuclideanSpace.single_apply] using this
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, h1]
  spectral_gap := by
    intro μ v hv h
    have h0 := congrFun (congrArg WithLp.ofLp h) 0
    have h1 := congrFun (congrArg WithLp.ofLp h) 1
    simp only [toyHam, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.single_apply,
      PiLp.smul_apply, smul_eq_mul, if_true, if_neg (by decide : ¬((0 : Fin 2) = 1))] at h0 h1
    by_cases hv0 : v.ofLp 0 = 0
    · right
      have hv1 : v.ofLp 1 ≠ 0 := by
        intro hz
        apply hv
        ext i
        fin_cases i <;> simp [hv0, hz]
      have hmu : ((μ : ℂ) - 1) * v.ofLp 1 = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp hmu with hc | hc
      · have hc' : (μ : ℂ) = 1 := by linear_combination hc
        have : μ = 1 := by exact_mod_cast hc'
        simp [this]
      · exact absurd hc hv1
    · left
      rcases mul_eq_zero.mp h0.symm with hc | hc
      · exact_mod_cast hc
      · exact absurd hc hv0

end LSM

end Phys

