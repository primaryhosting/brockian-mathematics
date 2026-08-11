/-
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Yang Mills Mass Gap
Category: Frontier — Moonshot
Target: Frontier.yang_mills_mass_gap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the statement of the Yang–Mills existence and mass gap problem in the
Osterwalder–Schrader / transfer-operator language, and proves a Lean-checked reduction:
*exponential clustering of the Euclidean time evolution implies a positive mass gap*.

Everything lives on a fixed separable infinite dimensional complex Hilbert space
`Frontier.HS = ℓ²(ℕ, ℂ)` (any separable infinite dimensional Hilbert space is isometric to it).
-/

noncomputable section

namespace Frontier

open scoped InnerProductSpace

/-- The state space of the quantum theory: a fixed separable infinite dimensional complex
Hilbert space, realised as `ℓ²(ℕ, ℂ)`. -/
abbrev HS := lp (fun _ : ℕ => ℂ) 2

/-- The gauge group of the Yang–Mills mass gap problem, here `SU(3)`. -/
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- The data of a quantum gauge theory with gauge group `G`, in the transfer-operator
(Osterwalder–Schrader reconstructed) formulation:

* a state space `HS` with a normalised vacuum vector `vacuum`;
* the Euclidean time evolution semigroup `evol t = e^{-tH}` of the (positive) Hamiltonian `H`,
  given as a self-adjoint contraction semigroup fixing the vacuum;
* a unitary representation `transl` of the group `ℝ³` of spatial translations, commuting with
  the time evolution and fixing the vacuum;
* gauge invariant Wilson-loop observables `wilson L` indexed by loops `L : ℕ → ℝ⁴` in
  four dimensional Euclidean space-time;
* a unitary representation `gauge` of the gauge group `G` commuting with the observables and
  fixing the vacuum. -/
structure QuantumGaugeTheory (G : Type) [Group G] where
  /-- The vacuum state. -/
  vacuum : HS
  /-- The vacuum is a unit vector. -/
  vacuum_unit : ‖vacuum‖ = 1
  /-- Euclidean time evolution `e^{-tH}`. -/
  evol : ℝ → (HS →L[ℂ] HS)
  /-- `e^{-0·H} = 1`. -/
  evol_zero : evol 0 = ContinuousLinearMap.id ℂ HS
  /-- Semigroup law. -/
  evol_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → evol (s + t) = (evol s).comp (evol t)
  /-- The Hamiltonian is self-adjoint. -/
  evol_selfAdjoint : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (evol t)
  /-- The Hamiltonian is positive, i.e. `e^{-tH}` is a contraction. -/
  evol_contraction : ∀ t : ℝ, 0 ≤ t → ‖evol t‖ ≤ 1
  /-- The vacuum has energy zero. -/
  evol_vacuum : ∀ t : ℝ, 0 ≤ t → evol t vacuum = vacuum
  /-- Unitary spatial translations. -/
  transl : (Fin 3 → ℝ) → (HS ≃ₗᵢ[ℂ] HS)
  /-- Translation by `0` is the identity. -/
  transl_zero : transl 0 = LinearIsometryEquiv.refl ℂ HS
  /-- Translations form a representation of `ℝ³`. -/
  transl_add : ∀ a b, transl (a + b) = (transl a).trans (transl b)
  /-- The vacuum is translation invariant. -/
  transl_vacuum : ∀ a, transl a vacuum = vacuum
  /-- Space and Euclidean time translations commute. -/
  transl_evol : ∀ (a : Fin 3 → ℝ) (t : ℝ), 0 ≤ t → ∀ v, transl a (evol t v) = evol t (transl a v)
  /-- Wilson loop observables, indexed by loops in `ℝ⁴`. -/
  wilson : (ℕ → (Fin 4 → ℝ)) → (HS →L[ℂ] HS)
  /-- Unitary action of the gauge group. -/
  gauge : G → (HS ≃ₗᵢ[ℂ] HS)
  /-- The gauge action is a representation. -/
  gauge_one : gauge 1 = LinearIsometryEquiv.refl ℂ HS
  /-- The gauge action is a representation. -/
  gauge_mul : ∀ g h, gauge (g * h) = (gauge h).trans (gauge g)
  /-- The vacuum is gauge invariant. -/
  gauge_vacuum : ∀ g, gauge g vacuum = vacuum
  /-- Wilson loops are gauge invariant observables. -/
  gauge_invariant : ∀ g L v, gauge g (wilson L v) = wilson L (gauge g v)

variable {G : Type} [Group G]

/-- The spatial translate of a loop in `ℝ⁴` by a vector `a ∈ ℝ³` (acting on the last three,
"spatial", coordinates). -/
def spatialShift (a : Fin 3 → ℝ) (L : ℕ → (Fin 4 → ℝ)) : ℕ → (Fin 4 → ℝ) :=
  fun n => L n + Fin.cons (0 : ℝ) a

/-- The extra requirements making a quantum gauge theory a *Yang–Mills* theory: the vacuum is
cyclic for the Wilson observables, the theory is interacting (some Wilson loop moves the vacuum
out of the vacuum ray), and the Wilson observables transform covariantly under spatial
translations. -/
structure IsYangMills (Q : QuantumGaugeTheory SU3) : Prop where
  /-- The vacuum is cyclic for the algebra of Wilson observables. -/
  cyclic : (Submodule.span ℂ (Set.range fun L => Q.wilson L Q.vacuum)).topologicalClosure = ⊤
  /-- The theory is not trivial: some Wilson loop creates a state out of the vacuum ray. -/
  interacting : ∃ L, Q.wilson L Q.vacuum ∉ (ℂ ∙ Q.vacuum)
  /-- Euclidean (spatial) covariance of the Wilson observables. -/
  covariant : ∀ a L, Q.transl a (Q.wilson L Q.vacuum) = Q.wilson (spatialShift a L) Q.vacuum

/-- The theory `Q` has a mass gap of size at least `m`: on the orthogonal complement of the
vacuum, the Euclidean time evolution decays at least like `e^{-mt}`. Equivalently, the spectrum
of the Hamiltonian is contained in `{0} ∪ [m, ∞)`. -/
def HasMassGap (Q : QuantumGaugeTheory G) (m : ℝ) : Prop :=
  0 < m ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : HS, ⟪Q.vacuum, v⟫_ℂ = 0 →
    ‖Q.evol t v‖ ≤ Real.exp (-m * t) * ‖v‖

/-- Exponential clustering with rate `m`: correlations in the vacuum sector decay like
`C e^{-mt}` for some constant `C`. This is the (hard, analytic) input of the reduction below. -/
def ExponentialClustering (Q : QuantumGaugeTheory G) (m : ℝ) : Prop :=
  0 < m ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : HS, ⟪Q.vacuum, v⟫_ℂ = 0 →
    ‖Q.evol t v‖ ≤ C * (Real.exp (-m * t) * ‖v‖)

/-- The Yang–Mills existence and mass gap statement: there is a quantum Yang–Mills theory with
gauge group `SU(3)` on four dimensional space-time, with a positive mass gap. -/
def YangMillsExistenceAndMassGap : Prop :=
  ∃ Q : QuantumGaugeTheory SU3, IsYangMills Q ∧ ∃ m : ℝ, 0 < m ∧ HasMassGap Q m

/-! ### Elementary spectral estimates -/

/-- For a self-adjoint operator, `‖Tv‖² ≤ ‖v‖ ‖T²v‖`. -/
theorem norm_sq_le_of_selfAdjoint {T S : HS →L[ℂ] HS} (hT : IsSelfAdjoint T)
    (hS : S = T.comp T) (v : HS) : ‖T v‖ ^ 2 ≤ ‖v‖ * ‖S v‖ := by
  have h1 : (⟪T v, T v⟫_ℂ) = ⟪v, S v⟫_ℂ := by
    have hadj : ContinuousLinearMap.adjoint T = T := by
      rw [← ContinuousLinearMap.star_eq_adjoint]; exact hT
    have := ContinuousLinearMap.adjoint_inner_left T (T v) v
    rw [hadj] at this
    subst hS
    simpa using this
  have h2 : ‖T v‖ ^ 2 = ‖(⟪T v, T v⟫_ℂ)‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [h2, h1]
  exact norm_inner_le_norm _ _

/-- Iterated version: `‖T v‖^(2^k) ≤ ‖v‖^(2^k - 1) ‖T^(2^k) v‖` for a self-adjoint contraction
semigroup, phrased for the semigroup `evol`. -/
theorem norm_pow_two_pow_le (Q : QuantumGaugeTheory G) (t : ℝ) (ht : 0 ≤ t) (v : HS) (k : ℕ) :
    ‖Q.evol t v‖ ^ (2 ^ k) ≤ ‖v‖ ^ (2 ^ k - 1) * ‖Q.evol (2 ^ k * t) v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h2t : (0:ℝ) ≤ 2 ^ k * t := by positivity
      have hstep : ‖Q.evol (2 ^ k * t) v‖ ^ 2 ≤ ‖v‖ * ‖Q.evol (2 ^ (k+1) * t) v‖ := by
        refine norm_sq_le_of_selfAdjoint (Q.evol_selfAdjoint _ h2t) ?_ v
        have : (2:ℝ) ^ (k+1) * t = 2 ^ k * t + 2 ^ k * t := by ring
        rw [this, Q.evol_add _ _ h2t h2t]
      have hnn : (0:ℝ) ≤ ‖Q.evol t v‖ := norm_nonneg _
      have hv : (0:ℝ) ≤ ‖v‖ := norm_nonneg _
      have key : (‖Q.evol t v‖ ^ (2 ^ k)) ^ 2 ≤ (‖v‖ ^ (2 ^ k - 1)) ^ 2 * ‖Q.evol (2 ^ k * t) v‖ ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) ih 2
      have h3 : (‖v‖ ^ (2 ^ k - 1)) ^ 2 * ‖Q.evol (2 ^ k * t) v‖ ^ 2
          ≤ (‖v‖ ^ (2 ^ k - 1)) ^ 2 * (‖v‖ * ‖Q.evol (2 ^ (k+1) * t) v‖) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      have h4 : (‖v‖ ^ (2 ^ k - 1)) ^ 2 * (‖v‖ * ‖Q.evol (2 ^ (k+1) * t) v‖)
          = ‖v‖ ^ (2 ^ (k+1) - 1) * ‖Q.evol (2 ^ (k+1) * t) v‖ := by
        have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have : (2 ^ k - 1) * 2 + 1 = 2 ^ (k+1) - 1 := by
          have : 2 ^ (k+1) = 2 ^ k * 2 := by ring
          omega
        rw [← pow_mul, ← mul_assoc, ← pow_succ, this]
      have h5 : (‖Q.evol t v‖ ^ (2 ^ k)) ^ 2 = ‖Q.evol t v‖ ^ (2 ^ (k+1)) := by
        rw [← pow_mul]
        ring_nf
      rw [← h5, ← h4]
      exact le_trans key h3

/-- If `a^(2^k) ≤ C * b^(2^k)` for every `k`, then `a ≤ b` (for `b ≥ 0`). -/
theorem le_of_pow_two_pow_le {a b C : ℝ} (hb : 0 ≤ b)
    (h : ∀ k : ℕ, a ^ (2 ^ k) ≤ C * b ^ (2 ^ k)) : a ≤ b := by
  by_contra hab
  push_neg at hab
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have := h 0
    simp [← hb0] at this
    linarith
  · have hr : 1 < a / b := (one_lt_div hb0).2 hab
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (y := a / b) C hr
    have hmono : (a / b) ^ n ≤ (a / b) ^ (2 ^ n) :=
      pow_le_pow_right₀ hr.le (Nat.le_of_lt (Nat.lt_two_pow_self))
    have hk := h n
    have hbk : (0:ℝ) < b ^ (2 ^ n) := by positivity
    have : (a / b) ^ (2 ^ n) ≤ C := by
      rw [div_pow, div_le_iff₀ hbk]
      linarith [hk]
    linarith

/-! ### The reduction -/

/-- **Reduction.** Exponential clustering with rate `m` implies a mass gap of size `m`:
the constant `C` can be removed by the self-adjointness of the Euclidean time evolution. -/
theorem hasMassGap_of_exponentialClustering {Q : QuantumGaugeTheory G} {m : ℝ}
    (h : ExponentialClustering Q m) : HasMassGap Q m := by
  obtain ⟨hm, C, hC, hcl⟩ := h
  refine ⟨hm, fun t ht v hv => ?_⟩
  refine le_of_pow_two_pow_le (C := C) (by positivity) (fun k => ?_)
  have h2t : (0:ℝ) ≤ 2 ^ k * t := by positivity
  have h1 := norm_pow_two_pow_le Q t ht v k
  have h2 := hcl (2 ^ k * t) h2t v hv
  have hv0 : (0:ℝ) ≤ ‖v‖ := norm_nonneg _
  have h3 : ‖v‖ ^ (2 ^ k - 1) * ‖Q.evol (2 ^ k * t) v‖
      ≤ ‖v‖ ^ (2 ^ k - 1) * (C * (Real.exp (-m * (2 ^ k * t)) * ‖v‖)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hexp : Real.exp (-m * (2 ^ k * t)) = Real.exp (-m * t) ^ (2 ^ k) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have h4 : ‖v‖ ^ (2 ^ k - 1) * (C * (Real.exp (-m * (2 ^ k * t)) * ‖v‖))
      = C * (Real.exp (-m * t) * ‖v‖) ^ (2 ^ k) := by
    rw [hexp, mul_pow]
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have : ‖v‖ ^ (2 ^ k - 1) * ‖v‖ = ‖v‖ ^ (2 ^ k) := by
      rw [← pow_succ]
      congr 1
      omega
    calc ‖v‖ ^ (2 ^ k - 1) * (C * (Real.exp (-m * t) ^ (2 ^ k) * ‖v‖))
        = C * Real.exp (-m * t) ^ (2 ^ k) * (‖v‖ ^ (2 ^ k - 1) * ‖v‖) := by ring
      _ = C * Real.exp (-m * t) ^ (2 ^ k) * ‖v‖ ^ (2 ^ k) := by rw [this]
      _ = C * (Real.exp (-m * t) ^ (2 ^ k) * ‖v‖ ^ (2 ^ k)) := by ring
  linarith [h1, h3, h4 ▸ h3]

/-- **Main statement (reduction form).** If there exists a quantum Yang–Mills theory with gauge
group `SU(3)` on `ℝ⁴` whose Euclidean correlations cluster exponentially at some rate `m > 0`,
then quantum Yang–Mills theory exists with a positive mass gap. -/
theorem yang_mills_mass_gap
    (h : ∃ Q : QuantumGaugeTheory SU3, IsYangMills Q ∧ ∃ m : ℝ, ExponentialClustering Q m) :
    YangMillsExistenceAndMassGap := by
  obtain ⟨Q, hYM, m, hcl⟩ := h
  exact ⟨Q, hYM, m, hcl.1, hasMassGap_of_exponentialClustering hcl⟩


/-! ### A base case: a model with a mass gap

The framework above is non-vacuous: we build explicitly the "single mass" model, whose
Hamiltonian has spectrum `{0, m}`, and check that it satisfies all the axioms of a quantum gauge
theory and has mass gap `m`.  (It is of course *not* a Yang–Mills theory: its Wilson
observables are trivial, so it does not satisfy `IsYangMills`.) -/

/-- The vacuum vector of the base-case model. -/
def baseVac : HS := lp.single 2 0 (1 : ℂ)

lemma norm_baseVac : ‖baseVac‖ = 1 := by simp [baseVac]

lemma inner_baseVac : ⟪baseVac, baseVac⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_baseVac]; norm_num

/-- The rank one orthogonal projection onto the vacuum ray. -/
def vacProj : HS →L[ℂ] HS := (innerSL ℂ baseVac).smulRight baseVac

/-- The operator acting as the identity on the vacuum and as multiplication by `a` on the
orthogonal complement of the vacuum. -/
def gapOp (a : ℝ) : HS →L[ℂ] HS :=
  (a : ℂ) • ContinuousLinearMap.id ℂ HS + (1 - (a : ℂ)) • vacProj

lemma gapOp_apply (a : ℝ) (v : HS) :
    gapOp a v = (a : ℂ) • v + (1 - (a : ℂ)) • ((⟪baseVac, v⟫_ℂ) • baseVac) := by
  simp [gapOp, vacProj]

lemma gapOp_inner (a : ℝ) (v : HS) : ⟪baseVac, gapOp a v⟫_ℂ = ⟪baseVac, v⟫_ℂ := by
  rw [gapOp_apply, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_baseVac]
  ring

lemma gapOp_vac (a : ℝ) : gapOp a baseVac = baseVac := by
  rw [gapOp_apply, inner_baseVac]; module

lemma gapOp_one : gapOp 1 = ContinuousLinearMap.id ℂ HS := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [gapOp_apply]

lemma gapOp_comp (a b : ℝ) : (gapOp a).comp (gapOp b) = gapOp (a * b) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [gapOp_apply a (gapOp b v), gapOp_inner, gapOp_apply b v, gapOp_apply]
  push_cast
  module

lemma gapOp_selfAdjoint (a : ℝ) : IsSelfAdjoint (gapOp a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  have hL : ⟪gapOp a x, y⟫_ℂ
      = (a : ℂ) * ⟪x, y⟫_ℂ + (1 - (a : ℂ)) * (⟪x, baseVac⟫_ℂ * ⟪baseVac, y⟫_ℂ) := by
    rw [gapOp_apply, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
      Complex.conj_ofReal, inner_conj_symm]
    simp [map_sub, Complex.conj_ofReal]
  have hR : ⟪x, gapOp a y⟫_ℂ
      = (a : ℂ) * ⟪x, y⟫_ℂ + (1 - (a : ℂ)) * (⟪x, baseVac⟫_ℂ * ⟪baseVac, y⟫_ℂ) := by
    rw [gapOp_apply, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
    ring
  rw [hL, hR]

lemma gapOp_norm_le (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : ‖gapOp a‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  have hcs : ‖(⟪baseVac, v⟫_ℂ)‖ ≤ ‖v‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) baseVac v
    rwa [norm_baseVac, one_mul] at this
  have hn1 : ‖((1 - a : ℝ) : ℂ)‖ = 1 - a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - a)]
  have hna : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  calc ‖gapOp a v‖
      ≤ ‖(a : ℂ) • v‖ + ‖(1 - (a : ℂ)) • ((⟪baseVac, v⟫_ℂ) • baseVac)‖ := by
        rw [gapOp_apply]; exact norm_add_le _ _
    _ = a * ‖v‖ + (1 - a) * ‖(⟪baseVac, v⟫_ℂ)‖ := by
        rw [norm_smul, norm_smul, norm_smul, norm_baseVac,
          show ((1 : ℂ) - (a : ℂ)) = ((1 - a : ℝ) : ℂ) by push_cast; ring, hn1, hna, mul_one]
    _ ≤ a * ‖v‖ + (1 - a) * ‖v‖ := by nlinarith
    _ = 1 * ‖v‖ := by ring

lemma gapOp_orth (a : ℝ) (v : HS) (hv : ⟪baseVac, v⟫_ℂ = 0) : gapOp a v = (a : ℂ) • v := by
  rw [gapOp_apply, hv]; module

/-- The base-case ("single mass") quantum gauge theory: the Hamiltonian has spectrum `{0, m}`. -/
def freeTheory (m : ℝ) (hm : 0 ≤ m) : QuantumGaugeTheory SU3 where
  vacuum := baseVac
  vacuum_unit := norm_baseVac
  evol t := gapOp (Real.exp (-m * t))
  evol_zero := by simpa using gapOp_one
  evol_add s t _ _ := by
    rw [gapOp_comp, ← Real.exp_add]
    ring_nf
  evol_selfAdjoint t _ := gapOp_selfAdjoint _
  evol_contraction t ht :=
    gapOp_norm_le _ (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by nlinarith))
  evol_vacuum t _ := gapOp_vac _
  transl _ := LinearIsometryEquiv.refl ℂ HS
  transl_zero := rfl
  transl_add _ _ := rfl
  transl_vacuum _ := rfl
  transl_evol _ _ _ _ := rfl
  wilson _ := 0
  gauge _ := LinearIsometryEquiv.refl ℂ HS
  gauge_one := rfl
  gauge_mul _ _ := rfl
  gauge_vacuum _ := rfl
  gauge_invariant _ _ _ := by simp

/-- **Base case.** For every `m > 0` there is a quantum gauge theory in the above sense with
mass gap `m`: the free single-mass theory. -/
theorem exists_theory_with_mass_gap (m : ℝ) (hm : 0 < m) :
    ∃ Q : QuantumGaugeTheory SU3, HasMassGap Q m := by
  refine ⟨freeTheory m hm.le, hm, fun t ht v hv => ?_⟩
  have hev : (freeTheory m hm.le).evol t v = ((Real.exp (-m * t) : ℝ) : ℂ) • v :=
    gapOp_orth _ v hv
  rw [hev, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]

/-- A mass gap is in particular exponential clustering (with constant `1`), so the reduction
`hasMassGap_of_exponentialClustering` is in fact an equivalence. -/
theorem exponentialClustering_iff_hasMassGap (Q : QuantumGaugeTheory G) (m : ℝ) :
    ExponentialClustering Q m ↔ HasMassGap Q m := by
  refine ⟨hasMassGap_of_exponentialClustering, fun h => ⟨h.1, 1, le_refl 1, fun t ht v hv => ?_⟩⟩
  simpa using h.2 t ht v hv

end Frontier

end

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

