/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## Setting

We work in three-dimensional configuration space.  A many-body fermionic state is
described here by the two quantities that enter the Lieb–Thirring argument:

* its total kinetic energy `T = ⟨Ψ, (-Δ₁ - ⋯ - Δ_N) Ψ⟩`,
* its one-body density `ρ`, normalised by `∫ ρ = N`.

The deep analytic input of the theory — the Lieb–Thirring inequality at `γ = 1` in
dimension `3` — is recorded as the predicate `LiebThirringBound`.  It is stated in
its *variational* form, which is the form in which it is used, and which is
equivalent to the eigenvalue-sum formulation by the min–max principle: for every
external potential `V`, the energy of the state in `-Δ + V` is bounded below by
`- L ∫ V₋^{5/2}`.

Everything below this input is proved here:

* `legendre_pointwise` — the pointwise Legendre/Young inequality, obtained from
  Mathlib's `Real.young_inequality` for the Hölder-conjugate pair `(5/2, 5/3)`;
* `kinetic_energy_bound` — the duality passage to the Thomas–Fermi-type kinetic
  energy inequality `T ≥ K_L ∫ ρ^{5/3}`, with the explicit constant
  `K_L = (3/5)(2/(5L))^{2/3}`;
* `liebThirringBound_of_kinetic` — the converse, showing that the two forms are in
  fact equivalent (so the hypothesis is not vacuous);
* `integral_rpow_four_thirds_le` — the Hölder interpolation
  `∫ ρ^{4/3} ≤ (∫ρ)^{1/2} (∫ρ^{5/3})^{1/2}`, obtained from Mathlib's
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`;
* `lieb_thirring_stability` — stability of matter of the second kind,
  `E ≥ -C·(N + K)`.
-/

/-- Configuration space of a single particle: three-dimensional Euclidean space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- The negative part `V₋ = max (-V) 0` of a potential (a nonnegative function). -/
noncomputable def potNegPart (V : Space → ℝ) (x : Space) : ℝ := max (-V x) 0

lemma potNegPart_nonneg (V : Space → ℝ) (x : Space) : 0 ≤ potNegPart V x :=
  le_max_right _ _

/-- A nonnegative potential has vanishing negative part; this is the trivial base
case of the Lieb–Thirring inequality (no negative spectrum, empty eigenvalue sum). -/
lemma potNegPart_of_nonneg {V : Space → ℝ} (hV : ∀ x, 0 ≤ V x) (x : Space) :
    potNegPart V x = 0 :=
  max_eq_right (by simpa using hV x)

/-- The Thomas–Fermi kinetic constant produced by a Lieb–Thirring bound with
constant `L`: it is the value `K_L = (3/5) (2/(5L))^{2/3}` of the Legendre
transform. -/
noncomputable def ltKineticConst (L : ℝ) : ℝ := (3 / 5) * (2 / (5 * L)) ^ ((2 : ℝ) / 3)

lemma ltKineticConst_pos {L : ℝ} (hL : 0 < L) : 0 < ltKineticConst L := by
  have : (0:ℝ) < 2 / (5 * L) := by positivity
  unfold ltKineticConst
  positivity

/-- **The Lieb–Thirring inequality (γ = 1, d = 3), variational form.**

`LiebThirringBound L T ρ` says: for the many-body state with kinetic energy `T` and
one-body density `ρ`, and for every external potential `V` (subject to the
integrability that makes both sides finite), the total energy of the state in the
field `V` obeys

`T + ∫ V ρ ≥ - L ∫ V₋^{5/2}`,

only the negative part of `V` being relevant.  By the min–max principle this is
equivalent to the eigenvalue-sum form `∑_j |E_j(-Δ+V)| ≤ L ∫ V₋^{5/2}` of the
Lieb–Thirring inequality at `γ = 1` in dimension three. -/
def LiebThirringBound (L T : ℝ) (ρ : Space → ℝ) : Prop :=
  ∀ V : Space → ℝ,
    Integrable (fun x => potNegPart V x * ρ x) →
    Integrable (fun x => potNegPart V x ^ ((5 : ℝ) / 2)) →
    -L * ∫ x, potNegPart V x ^ ((5 : ℝ) / 2) ≤ T - ∫ x, potNegPart V x * ρ x

/-!
## Step 0: the pointwise Legendre (Young) inequality
-/

/-- Pointwise Legendre duality: `v r - L v^{5/2} ≤ K_L r^{5/3}` for `v, r ≥ 0`.

This is Mathlib's Young inequality `Real.young_inequality` for the Hölder-conjugate
pair `(5/2, 5/3)`, used with the optimal scaling `λ = (5L/2)^{2/5}`; the resulting
constant `K_L` is exactly the Legendre transform value. -/
theorem legendre_pointwise {L v r : ℝ} (hL : 0 < L) (hv : 0 ≤ v) (hr : 0 ≤ r) :
    v * r - L * v ^ ((5 : ℝ) / 2) ≤ ltKineticConst L * r ^ ((5 : ℝ) / 3) := by
  have hA : (0:ℝ) < 5 * L / 2 := by linarith
  set lam : ℝ := (5 * L / 2) ^ ((2 : ℝ) / 5) with hlam
  have hlampos : 0 < lam := Real.rpow_pos_of_pos hA _
  have hcj : Real.HolderConjugate (5 / 2) (5 / 3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have key := Real.young_inequality (lam * v) (r / lam) hcj
  have h1 : (lam * v) * (r / lam) = v * r := by field_simp
  rw [h1, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam * v),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ r / lam)] at key
  have e1 : (lam * v) ^ ((5 : ℝ) / 2) = (5 * L / 2) * v ^ ((5 : ℝ) / 2) := by
    rw [Real.mul_rpow hlampos.le hv, hlam, ← Real.rpow_mul hA.le]
    norm_num
  have hinv : (2 : ℝ) / (5 * L) = (5 * L / 2)⁻¹ := by field_simp
  have e2 : (r / lam) ^ ((5 : ℝ) / 3)
      = (2 / (5 * L)) ^ ((2 : ℝ) / 3) * r ^ ((5 : ℝ) / 3) := by
    rw [Real.div_rpow hr hlampos.le, hlam, ← Real.rpow_mul hA.le, hinv,
      Real.inv_rpow hA.le]
    norm_num [div_eq_mul_inv, mul_comm]
  rw [e1, e2] at key
  simp only [ltKineticConst]
  linarith [key]

/-!
## Step 1: from the Lieb–Thirring inequality to the kinetic energy inequality
-/

/-- **Lieb–Thirring kinetic energy inequality.**  The Lieb–Thirring bound at
`γ = 1` implies the Thomas–Fermi-type lower bound `T ≥ K_L ∫ ρ^{5/3}` for the
kinetic energy of a state in terms of its one-body density.

The proof is the Legendre duality argument: test the variational bound against the
potential `V = -K ρ^{2/3}` with the optimal coupling `K = (2/(5L))^{2/3}`. -/
theorem kinetic_energy_bound {L T : ℝ} {ρ : Space → ℝ} (hL : 0 < L)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hint53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)))
    (hLT : LiebThirringBound L T ρ) :
    ltKineticConst L * ∫ x, ρ x ^ ((5 : ℝ) / 3) ≤ T := by
  have hApos : (0:ℝ) < 2 / (5 * L) := by positivity
  set A : ℝ := 2 / (5 * L) with hA
  set c : ℝ := A ^ ((2 : ℝ) / 3) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hApos _
  set V : Space → ℝ := fun x => -(c * ρ x ^ ((2 : ℝ) / 3)) with hV
  have hnp : ∀ x, potNegPart V x = c * ρ x ^ ((2 : ℝ) / 3) := by
    intro x
    show max (-(V x)) 0 = _
    simp only [hV, neg_neg]
    exact max_eq_left (mul_nonneg hcpos.le (Real.rpow_nonneg (hρ0 x) _))
  have hB : ∀ x, potNegPart V x * ρ x = c * ρ x ^ ((5 : ℝ) / 3) := by
    intro x
    rw [hnp, mul_assoc]
    congr 1
    nth_rewrite 2 [← Real.rpow_one (ρ x)]
    rw [← Real.rpow_add' (hρ0 x) (by norm_num)]
    norm_num
  have hC : ∀ x, potNegPart V x ^ ((5 : ℝ) / 2)
      = c ^ ((5 : ℝ) / 2) * ρ x ^ ((5 : ℝ) / 3) := by
    intro x
    rw [hnp, Real.mul_rpow hcpos.le (Real.rpow_nonneg (hρ0 x) _),
      ← Real.rpow_mul (hρ0 x)]
    norm_num
  have hi1 : Integrable (fun x => potNegPart V x * ρ x) := by
    simp only [hB]; exact hint53.const_mul _
  have hi2 : Integrable (fun x => potNegPart V x ^ ((5 : ℝ) / 2)) := by
    simp only [hC]; exact hint53.const_mul _
  have key := hLT V hi1 hi2
  simp only [hB, hC, integral_const_mul] at key
  have hpow : c ^ ((5 : ℝ) / 2) = c * A := by
    have h1 : c ^ ((5 : ℝ) / 2) = A ^ ((5 : ℝ) / 3) := by
      rw [hc, ← Real.rpow_mul hApos.le]; norm_num
    rw [h1, show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add hApos,
      Real.rpow_one, ← hc]
  rw [hpow] at key
  set S : ℝ := ∫ x, ρ x ^ ((5 : ℝ) / 3) with hSdef
  have hS : 0 ≤ S := integral_nonneg fun x => Real.rpow_nonneg (hρ0 x) _
  have hLA : L * A = 2 / 5 := by rw [hA]; field_simp
  have hrw : L * (c * A * S) = (2 / 5) * (c * S) := by
    have h : L * (c * A * S) = (L * A) * (c * S) := by ring
    rw [h, hLA]
  have hK : ltKineticConst L = (3 / 5) * c := rfl
  rw [hK]
  nlinarith [key, hrw]

/-- The converse of `kinetic_energy_bound`: the kinetic energy inequality with the
constant `K_L` implies back the Lieb–Thirring variational bound with constant `L`.

In particular the hypothesis `LiebThirringBound` is *not* vacuous: it holds for a
pair `(T, ρ)` exactly when the Thomas–Fermi bound `T ≥ K_L ∫ ρ^{5/3}` does. -/
theorem liebThirringBound_of_kinetic {L T : ℝ} {ρ : Space → ℝ} (hL : 0 < L)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hint53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)))
    (hT : ltKineticConst L * ∫ x, ρ x ^ ((5 : ℝ) / 3) ≤ T) :
    LiebThirringBound L T ρ := by
  intro V hi1 hi2
  have hf : Integrable
      (fun x => potNegPart V x * ρ x - L * potNegPart V x ^ ((5 : ℝ) / 2)) :=
    hi1.sub (hi2.const_mul L)
  have hg : Integrable (fun x => ltKineticConst L * ρ x ^ ((5 : ℝ) / 3)) :=
    hint53.const_mul _
  have hmono : ∫ x, (potNegPart V x * ρ x - L * potNegPart V x ^ ((5 : ℝ) / 2))
      ≤ ∫ x, ltKineticConst L * ρ x ^ ((5 : ℝ) / 3) :=
    integral_mono hf hg fun x => legendre_pointwise hL (potNegPart_nonneg V x) (hρ0 x)
  rw [integral_sub hi1 (hi2.const_mul L), integral_const_mul, integral_const_mul]
    at hmono
  linarith

/-- **Non-vacuity certificate.**  There is a genuinely nonzero one-electron state
(the uniform density on the unit ball, normalised to `∫ ρ = 1`) satisfying all the
hypotheses of the Lieb–Thirring bound `LiebThirringBound L T ρ`, for every `L > 0`.
So the hypotheses used below are consistent and not vacuously satisfiable only by
degenerate data. -/
theorem exists_nontrivial_liebThirring_state {L : ℝ} (hL : 0 < L) :
    ∃ (ρ : Space → ℝ) (T : ℝ),
      (∀ x, 0 ≤ ρ x) ∧ (∃ x, 0 < ρ x) ∧
      AEStronglyMeasurable ρ volume ∧ Integrable ρ ∧
      Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)) ∧
      (∫ x, ρ x) = 1 ∧ LiebThirringBound L T ρ := by
  set B : Set Space := Metric.ball 0 1 with hB
  have hmB : MeasurableSet B := measurableSet_ball
  have h1 : 0 < volume B := Metric.measure_ball_pos volume 0 one_pos
  have h2 : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hv : 0 < volume.real B := ENNReal.toReal_pos h1.ne' h2
  set k : ℝ := (volume.real B)⁻¹ with hk
  have hkpos : 0 < k := by positivity
  set ρ : Space → ℝ := Set.indicator B (fun _ => k) with hρ
  have hint : (∫ x, ρ x) = 1 := by
    rw [hρ, integral_indicator_const k hmB, smul_eq_mul, hk]
    field_simp
  have hpow : ∀ p : ℝ, p ≠ 0 →
      (fun x => ρ x ^ p) = Set.indicator B (fun _ => k ^ p) := by
    intro p hp
    funext x
    rw [hρ]
    by_cases hx : x ∈ B
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, Real.zero_rpow hp]
  have hgen : ∀ c : ℝ, Integrable (Set.indicator B (fun _ => c)) := by
    intro c
    refine IntegrableOn.integrable_indicator ?_ hmB
    haveI : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top h2⟩
    exact integrable_const c
  have hI1 : Integrable ρ := hgen k
  have hI53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)) := by
    rw [hpow _ (by norm_num)]; exact hgen _
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x =>
    Set.indicator_nonneg (fun _ _ => hkpos.le) x
  refine ⟨ρ, ltKineticConst L * ∫ x, ρ x ^ ((5 : ℝ) / 3), hρ0, ⟨0, ?_⟩,
    hI1.aestronglyMeasurable, hI1, hI53, hint,
    liebThirringBound_of_kinetic hL hρ0 hI53 le_rfl⟩
  rw [hρ, Set.indicator_of_mem (by simp [hB] : (0 : Space) ∈ B)]
  exact hkpos

/-!
## Step 2: Hölder interpolation
-/

/-- Interpolation `∫ ρ^{4/3} ≤ (∫ ρ)^{1/2} (∫ ρ^{5/3})^{1/2}`: the Cauchy–Schwarz
case of Hölder's inequality (Mathlib's
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`) applied to the factorisation
`ρ^{4/3} = ρ^{1/2} · ρ^{5/6}`. -/
theorem integral_rpow_four_thirds_le {ρ : Space → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hmeas : AEStronglyMeasurable ρ volume) (hint1 : Integrable ρ)
    (hint53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3))) :
    ∫ x, ρ x ^ ((4 : ℝ) / 3) ≤
      Real.sqrt (∫ x, ρ x) * Real.sqrt (∫ x, ρ x ^ ((5 : ℝ) / 3)) := by
  have hcj : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hfm : AEStronglyMeasurable (fun x => ρ x ^ ((1 : ℝ) / 2)) volume :=
    (hmeas.aemeasurable.pow_const _).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => ρ x ^ ((5 : ℝ) / 6)) volume :=
    (hmeas.aemeasurable.pow_const _).aestronglyMeasurable
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hfL : MemLp (fun x => ρ x ^ ((1 : ℝ) / 2)) (ENNReal.ofReal 2) volume := by
    rw [h2, MeasureTheory.memLp_two_iff_integrable_sq hfm]
    have h : ∀ x, (ρ x ^ ((1 : ℝ) / 2)) ^ 2 = ρ x := by
      intro x
      rw [← Real.rpow_natCast (ρ x ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul (hρ0 x)]
      norm_num
    simpa only [h] using hint1
  have hgL : MemLp (fun x => ρ x ^ ((5 : ℝ) / 6)) (ENNReal.ofReal 2) volume := by
    rw [h2, MeasureTheory.memLp_two_iff_integrable_sq hgm]
    have h : ∀ x, (ρ x ^ ((5 : ℝ) / 6)) ^ 2 = ρ x ^ ((5 : ℝ) / 3) := by
      intro x
      rw [← Real.rpow_natCast (ρ x ^ ((5 : ℝ) / 6)) 2, ← Real.rpow_mul (hρ0 x)]
      norm_num
    simpa only [h] using hint53
  have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hcj
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hρ0 x) ((1 : ℝ) / 2))
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hρ0 x) ((5 : ℝ) / 6))
    hfL hgL
  have e1 : ∀ x, ρ x ^ ((1 : ℝ) / 2) * ρ x ^ ((5 : ℝ) / 6) = ρ x ^ ((4 : ℝ) / 3) := by
    intro x; rw [← Real.rpow_add' (hρ0 x) (by norm_num)]; norm_num
  have e2 : ∀ x, (ρ x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = ρ x := by
    intro x; rw [← Real.rpow_mul (hρ0 x)]; norm_num
  have e3 : ∀ x, (ρ x ^ ((5 : ℝ) / 6)) ^ (2 : ℝ) = ρ x ^ ((5 : ℝ) / 3) := by
    intro x; rw [← Real.rpow_mul (hρ0 x)]; norm_num
  simp only [e1, e2, e3] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact key

/-!
## Step 3: the elementary optimisation
-/

/-- `k t - c √t ≥ - c²/(4k)` for `k > 0`, `t ≥ 0`. -/
theorem quadratic_lower_bound {k c t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    -(c ^ 2 / (4 * k)) ≤ k * t - c * Real.sqrt t := by
  set s := Real.sqrt t with hs
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht
  have h : k * t - c * s + c ^ 2 / (4 * k) = (2 * k * s - c) ^ 2 / (4 * k) := by
    rw [← hs2]; field_simp; ring
  have h2 : 0 ≤ (2 * k * s - c) ^ 2 / (4 * k) := div_nonneg (sq_nonneg _) (by linarith)
  linarith

/-!
## Step 4: stability of matter
-/

/-- **Stability of matter of the second kind, via the Lieb–Thirring inequality.**

Consider a state of `N` electrons and `Knuc` nuclei in `ℝ³` with kinetic energy `T`,
one-body density `ρ` normalised by `∫ ρ = N`, and total Coulomb energy `W`.

Assume:

* the Lieb–Thirring inequality at `γ = 1` with constant `L > 0` holds for the state
  (`hLT`), and
* the electrostatic (Baxter / Lieb–Yau type) bound
  `W ≥ -a ∫ ρ^{4/3} - b·Knuc` holds with constants `a, b ≥ 0` (`hCoulomb`).

Then the total energy `T + W` is bounded below *linearly* in the number of
particles,

`T + W ≥ -C · (N + Knuc)`,  with  `C = a²/(4 K_L) + b`,

a constant depending only on `L, a, b` and not on the state, the particle numbers,
or the nuclear positions.  This is stability of the second kind. -/
theorem lieb_thirring_stability
    {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {N Knuc : ℕ} {ρ : Space → ℝ} {T W : ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x)
    (hmeas : AEStronglyMeasurable ρ volume)
    (hint1 : Integrable ρ)
    (hint53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)))
    (hnorm : ∫ x, ρ x = (N : ℝ))
    (hLT : LiebThirringBound L T ρ)
    (hCoulomb : -a * (∫ x, ρ x ^ ((4 : ℝ) / 3)) - b * (Knuc : ℝ) ≤ W) :
    -(a ^ 2 / (4 * ltKineticConst L) + b) * ((N : ℝ) + (Knuc : ℝ)) ≤ T + W := by
  have hK := ltKineticConst_pos hL
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hKnn : (0 : ℝ) ≤ (Knuc : ℝ) := Nat.cast_nonneg Knuc
  -- kinetic energy bound
  have hTk : ltKineticConst L * ∫ x, ρ x ^ ((5 : ℝ) / 3) ≤ T :=
    kinetic_energy_bound hL hρ0 hint53 hLT
  have ht0 : 0 ≤ ∫ x, ρ x ^ ((5 : ℝ) / 3) :=
    integral_nonneg fun x => Real.rpow_nonneg (hρ0 x) _
  -- Hölder interpolation, using ∫ ρ = N
  have hs := integral_rpow_four_thirds_le hρ0 hmeas hint1 hint53
  rw [hnorm] at hs
  -- transport it through the electrostatic bound
  have hW : -(a * Real.sqrt (N : ℝ) * Real.sqrt (∫ x, ρ x ^ ((5 : ℝ) / 3)))
      - b * (Knuc : ℝ) ≤ W := by
    have h : a * ∫ x, ρ x ^ ((4 : ℝ) / 3)
        ≤ a * Real.sqrt (N : ℝ) * Real.sqrt (∫ x, ρ x ^ ((5 : ℝ) / 3)) :=
      calc a * ∫ x, ρ x ^ ((4 : ℝ) / 3)
          ≤ a * (Real.sqrt (N : ℝ) * Real.sqrt (∫ x, ρ x ^ ((5 : ℝ) / 3))) :=
            mul_le_mul_of_nonneg_left hs ha
        _ = a * Real.sqrt (N : ℝ) * Real.sqrt (∫ x, ρ x ^ ((5 : ℝ) / 3)) := by ring
    linarith [hCoulomb, h]
  -- optimise the resulting quadratic in √t
  have hq := quadratic_lower_bound (k := ltKineticConst L)
    (c := a * Real.sqrt (N : ℝ)) (t := ∫ x, ρ x ^ ((5 : ℝ) / 3)) hK ht0
  have hsq : (a * Real.sqrt (N : ℝ)) ^ 2 = a ^ 2 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hNnn]
  rw [hsq] at hq
  have hbase : -(a ^ 2 * (N : ℝ) / (4 * ltKineticConst L)) - b * (Knuc : ℝ) ≤ T + W := by
    linarith
  -- finally spread the constant over `N + Knuc`
  have hD : 0 ≤ a ^ 2 / (4 * ltKineticConst L) := by positivity
  have hsplit : a ^ 2 * (N : ℝ) / (4 * ltKineticConst L)
      = (a ^ 2 / (4 * ltKineticConst L)) * (N : ℝ) := by ring
  rw [hsplit] at hbase
  nlinarith [mul_nonneg hD hKnn, mul_nonneg hb hNnn]

end Frontier

