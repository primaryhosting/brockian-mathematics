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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

open ComplexConjugate

section LSM

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Momentum obstruction (core of the Lieb–Schultz–Mattis argument).**

If the translation operator `T` is an isometry, the twist operator `U` anticommutes with `T`
(this is the algebraic footprint of a *half-integer* spin per unit cell: the twist shifts the
momentum by `π`), and `ψ` is a translation eigenvector, then the twisted state `U ψ` is
orthogonal to `ψ`. -/
theorem twisted_state_orthogonal
    (T U : V →ₗ[ℂ] V) (ψ : V) (c : ℂ)
    (hTiso : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hTU : ∀ x : V, T (U x) = -(U (T x)))
    (hTψ : T ψ = c • ψ) (hc : ‖c‖ = 1) :
    ⟪ψ, U ψ⟫_ℂ = 0 := by
  have key : ⟪ψ, U ψ⟫_ℂ = -⟪ψ, U ψ⟫_ℂ := by
    have h1 : ⟪T ψ, T (U ψ)⟫_ℂ = ⟪ψ, U ψ⟫_ℂ := hTiso ψ (U ψ)
    have h2 : T (U ψ) = -(c • U ψ) := by
      rw [hTU ψ, hTψ, map_smul]
    rw [h2, hTψ, inner_smul_left, inner_neg_right, inner_smul_right] at h1
    have hcc : (starRingEnd ℂ) c * c = 1 := by
      rw [RCLike.conj_mul (K := ℂ) c, hc]
      norm_num
    calc ⟪ψ, U ψ⟫_ℂ = (starRingEnd ℂ) c * -(c * ⟪ψ, U ψ⟫_ℂ) := h1.symm
      _ = -(((starRingEnd ℂ) c * c) * ⟪ψ, U ψ⟫_ℂ) := by ring
      _ = -⟪ψ, U ψ⟫_ℂ := by rw [hcc]; ring
  have : (2 : ℂ) * ⟪ψ, U ψ⟫_ℂ = 0 := by linear_combination key
  simpa using this

/-- **Lieb–Schultz–Mattis theorem (abstract form): a half-integer-spin translation-invariant
chain is gapless or degenerate.**

Data:
* `V` — the (complex) Hilbert space of states of the chain;
* `H` — the Hamiltonian, translation invariant (`hHT`);
* `T` — the lattice translation, an isometry (`hTiso`);
* `U` — the Lieb–Schultz–Mattis twist operator, an isometry (`hUiso`), which *anticommutes*
  with the translation (`hTU`).  This anticommutation is exactly the statement that the twist
  shifts the momentum by `π`, which is what a half-odd-integer spin per unit cell produces;
* `ψ` — a normalized ground state of energy `E₀`;
* `htwist` — the variational bound saying that the twisted state has energy at most `E₀ + ε`
  (for the physical chain of length `L`, `ε = O(1/L)`).

Conclusion (the LSM alternative): either the ground state is **degenerate** — there is another
ground state of the same energy `E₀`, orthogonal to `ψ` — or the system is **gapless** in the
sense that every candidate gap `Δ` below the excited spectrum obeys `Δ ≤ ε`. -/
theorem lieb_schultz_mattis
    (H T U : V →ₗ[ℂ] V) (ψ : V) (E₀ ε Δ : ℝ)
    (hTiso : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hUiso : ∀ x y : V, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hHT : ∀ x : V, H (T x) = T (H x))
    (hTU : ∀ x : V, T (U x) = -(U (T x)))
    (hψ : ‖ψ‖ = 1)
    (hgs : H ψ = (E₀ : ℂ) • ψ)
    (htwist : (⟪U ψ, H (U ψ)⟫_ℂ).re ≤ E₀ + ε)
    (hgap : ∀ v : V, ‖v‖ = 1 → ⟪ψ, v⟫_ℂ = 0 → E₀ + Δ ≤ (⟪v, H v⟫_ℂ).re) :
    (∃ v : V, ‖v‖ = 1 ∧ ⟪ψ, v⟫_ℂ = 0 ∧ H v = (E₀ : ℂ) • v) ∨ Δ ≤ ε := by
  by_cases hdeg : ∃ v : V, ‖v‖ = 1 ∧ ⟪ψ, v⟫_ℂ = 0 ∧ H v = (E₀ : ℂ) • v
  · exact Or.inl hdeg
  refine Or.inr ?_
  push_neg at hdeg
  -- Step 1: the ground state is a translation eigenvector.
  set c : ℂ := ⟪ψ, T ψ⟫_ℂ with hcdef
  set w : V := T ψ - c • ψ with hwdef
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hwperp : ⟪ψ, w⟫_ℂ = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hψψ, ← hcdef]
    ring
  have hHw : H w = (E₀ : ℂ) • w := by
    rw [hwdef, map_sub, map_smul, hgs, hHT ψ, hgs, map_smul]
    module
  have hw0 : w = 0 := by
    by_contra hne
    have hnorm : ‖w‖ ≠ 0 := by simpa using hne
    refine hdeg (((‖w‖ : ℝ) : ℂ)⁻¹ • w) ?_ ?_ ?_
    · rw [norm_smul]
      simp [inv_mul_cancel₀ hnorm]
    · rw [inner_smul_right, hwperp]; ring
    · rw [map_smul, hHw]
      module
  have hTψ : T ψ = c • ψ := by
    have := sub_eq_zero.mp (hwdef ▸ hw0)
    exact this
  have hcnorm : ‖c‖ = 1 := by
    have h1 : ‖T ψ‖ = ‖ψ‖ := by
      have := hTiso ψ ψ
      have h2 : ‖T ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
        rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
        exact congrArg Complex.re this
      nlinarith [norm_nonneg (T ψ), norm_nonneg ψ]
    rw [hTψ, norm_smul, hψ] at h1
    simpa [hψ] using h1
  -- Step 2: the twisted state is orthogonal to the ground state.
  have horth : ⟪ψ, U ψ⟫_ℂ = 0 :=
    twisted_state_orthogonal T U ψ c hTiso hTU hTψ hcnorm
  -- Step 3: the twisted state is a normalized trial state, so the gap is at most `ε`.
  have hUnorm : ‖U ψ‖ = 1 := by
    have h2 : ‖U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
      exact congrArg Complex.re (hUiso ψ ψ)
    rw [hψ] at h2
    nlinarith [norm_nonneg (U ψ)]
  have := hgap (U ψ) hUnorm horth
  linarith

/-- **Corollary (the LSM dichotomy in contrapositive form).**  Under the LSM hypotheses, a
translation-invariant half-integer-spin chain cannot simultaneously have a *unique* ground state
and a spectral gap `Δ` strictly larger than the twist energy `ε`. -/
theorem lieb_schultz_mattis_no_unique_gapped_ground_state
    (H T U : V →ₗ[ℂ] V) (ψ : V) (E₀ ε Δ : ℝ)
    (hTiso : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hUiso : ∀ x y : V, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hHT : ∀ x : V, H (T x) = T (H x))
    (hTU : ∀ x : V, T (U x) = -(U (T x)))
    (hψ : ‖ψ‖ = 1)
    (hgs : H ψ = (E₀ : ℂ) • ψ)
    (htwist : (⟪U ψ, H (U ψ)⟫_ℂ).re ≤ E₀ + ε)
    (hgap : ∀ v : V, ‖v‖ = 1 → ⟪ψ, v⟫_ℂ = 0 → E₀ + Δ ≤ (⟪v, H v⟫_ℂ).re)
    (hΔ : ε < Δ)
    (huniq : ∀ v : V, H v = (E₀ : ℂ) • v → ∃ c : ℂ, v = c • ψ) :
    False := by
  rcases lieb_schultz_mattis H T U ψ E₀ ε Δ hTiso hUiso hHT hTU hψ hgs htwist hgap with
    ⟨v, hv1, hv2, hv3⟩ | hle
  · obtain ⟨c, rfl⟩ := huniq v hv3
    have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
    rw [inner_smul_right, hψψ, mul_one] at hv2
    rw [hv2, zero_smul, norm_zero] at hv1
    exact zero_ne_one hv1
  · linarith

end LSM

section Example

/-! ### The hypotheses are not vacuous

A two-level example (a single half-integer spin): the "translation" is the Pauli matrix `σ_z`,
the twist operator is `σ_x` (these anticommute, which is the half-integer-spin input of LSM),
and the Hamiltonian is `diag (0, 1)`.  Here the ground state has energy `0`, the gap equals `1`,
and the twisted state indeed has energy `1 = E₀ + ε` with `ε = 1`. -/

/-- The "translation" operator of the two-level example: the Pauli matrix `σ_z`. -/
noncomputable def sigmaZ : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![1, 0; 0, -1]

/-- The twist operator of the two-level example: the Pauli matrix `σ_x`. -/
noncomputable def sigmaX : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, 1; 1, 0]

/-- The Hamiltonian of the two-level example: `diag (0, 1)`. -/
noncomputable def twoLevelHam : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, 0; 0, 1]

/-- The ground state of the two-level example. -/
noncomputable def twoLevelGround : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

/-- The hypotheses of `Phys.lieb_schultz_mattis` are satisfiable with a strictly positive gap
parameter `Δ`, so the theorem is not vacuous. -/
theorem lieb_schultz_mattis_hypotheses_nonvacuous :
    ∃ (H T U : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (ψ : EuclideanSpace ℂ (Fin 2)) (E₀ ε Δ : ℝ),
      0 < Δ ∧
      (∀ x y, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      (∀ x y, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      (∀ x, H (T x) = T (H x)) ∧
      (∀ x, T (U x) = -(U (T x))) ∧
      ‖ψ‖ = 1 ∧
      H ψ = (E₀ : ℂ) • ψ ∧
      (⟪U ψ, H (U ψ)⟫_ℂ).re ≤ E₀ + ε ∧
      (∀ v, ‖v‖ = 1 → ⟪ψ, v⟫_ℂ = 0 → E₀ + Δ ≤ (⟪v, H v⟫_ℂ).re) := by
  refine ⟨twoLevelHam, sigmaZ, sigmaX, twoLevelGround, 0, 1, 1, one_pos, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x y
    simp [sigmaZ, Matrix.toLpLin_apply, PiLp.inner_apply, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail]
  · intro x y
    simp [sigmaX, Matrix.toLpLin_apply, PiLp.inner_apply, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail]
    ring
  · intro x
    simp [twoLevelHam, sigmaZ, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail,
      PiLp.ext_iff, Fin.forall_fin_two]
  · intro x
    simp [sigmaZ, sigmaX, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail, PiLp.ext_iff,
      Fin.forall_fin_two]
  · simp [twoLevelGround]
  · simp only [twoLevelHam, twoLevelGround, Matrix.toLpLin_apply]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec]
  · simp [twoLevelHam, sigmaX, twoLevelGround, Matrix.toLpLin_apply, PiLp.inner_apply,
      Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two]
  · intro v hv hp
    have h0 : v.ofLp 0 = 0 := by
      simpa [twoLevelGround, PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.single_apply]
        using hp
    have h := EuclideanSpace.norm_eq v
    rw [hv] at h
    have hn : ∑ i, ‖v.ofLp i‖ ^ 2 = 1 := by
      have := Real.sqrt_eq_one.mp h.symm
      simpa using this
    rw [Fin.sum_univ_two, h0] at hn
    have hA : (0:ℝ) ≤ (v.ofLp 1).re * (v.ofLp 1).re + (v.ofLp 1).im * (v.ofLp 1).im := by
      nlinarith [mul_self_nonneg (v.ofLp 1).re, mul_self_nonneg (v.ofLp 1).im]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      Complex.norm_def, Complex.normSq_apply, Real.sq_sqrt hA] at hn
    simp [PiLp.inner_apply, Fin.sum_univ_two, h0, twoLevelHam, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail]
    linarith

end Example

end Phys

#print axioms Phys.lieb_schultz_mattis
#print axioms Phys.lieb_schultz_mattis_no_unique_gapped_ground_state
#print axioms Phys.lieb_schultz_mattis_hypotheses_nonvacuous

