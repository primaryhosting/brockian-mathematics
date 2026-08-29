/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

Li's criterion states that the Riemann Hypothesis is equivalent to the nonnegativity of the
Li coefficients
`λ_n = ∑_ρ (1 - (1 - 1/ρ)^n)`,
the sum running over the (nontrivial) zeros `ρ` of the Riemann zeta function, counted with
multiplicity.

Mathlib currently has no theory of the zero multiset of `ζ` (no Hadamard factorisation of the
completed zeta function `ξ`, no statement of RH), so the criterion cannot be stated for `ζ`
itself.  What *is* stated and proved here is the arithmetic-free core of the criterion, the
Bombieri–Lagarias positivity theorem, for a finite family of zeros:

For any finite family `ρ : ι → ℂ` of nonzero complex numbers (indexed by a `Finset s`, so that
multiplicities are allowed) which is closed under the functional-equation symmetry
`ρ ↦ 1 - ρ`, one has

  (all `ρ i` lie on the critical line `Re ρ = 1/2`)  ↔  (`λ_n ≥ 0` for every `n ≥ 1`).

Both directions are proved from scratch:

* the easy direction rests on the elementary equivalence `Re ρ ≥ 1/2 ↔ |1 - 1/ρ| ≤ 1`
  (`Frontier.norm_one_sub_inv_le_one_iff`);
* the hard direction is the finite Bombieri–Lagarias argument
  (`Frontier.norm_le_one_of_re_sum_pow_le`): if the real parts of the power sums
  `∑ᵢ zᵢ^n` stay bounded above, then every `zᵢ` lies in the closed unit disc.  This uses a
  recurrence (almost-periodicity) statement `Frontier.exists_pow_near_one`, proved by
  compactness of the polydisc, which produces arbitrarily large exponents `k` for which all the
  `k`-th powers of finitely many unimodular numbers are simultaneously close to `1`.

No lemma of Mathlib closes the statement (a search for `RiemannHypothesis`, `riemannXi` zero
multisets, or Bombieri–Lagarias positivity returns nothing); the Mathlib input used consists of
standard facts such as `tendsto_subseq_of_bounded`, `Complex.normSq_eq_norm_sq` and
`tendsto_pow_atTop_atTop_of_one_lt`.
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

set_option grind.warning false

open Filter

namespace Frontier

/-! ### The critical line in terms of the Li transform `ρ ↦ 1 - 1/ρ` -/

/-- The Li transform `ρ ↦ 1 - 1/ρ` maps the closed half plane `Re ρ ≥ 1/2` onto the closed
unit disc. -/
theorem norm_one_sub_inv_le_one_iff {z : ℂ} (hz : z ≠ 0) : ‖1 - 1 / z‖ ≤ 1 ↔ 1 / 2 ≤ z.re := by
  have h1 : ‖1 - 1 / z‖ = ‖z - 1‖ / ‖z‖ := by
    rw [← norm_div]; congr 1; field_simp
  have e1 : ‖z - 1‖ ^ 2 = (z.re - 1) * (z.re - 1) + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]
  have e2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]
  have h2 : (0 : ℝ) ≤ ‖z - 1‖ := norm_nonneg _
  have h3 : (0 : ℝ) < ‖z‖ := by simpa [norm_pos_iff] using hz
  rw [h1, div_le_one h3]
  constructor <;> intro h <;> nlinarith [h]

/-! ### A recurrence lemma for finitely many unimodular numbers -/

/-- Crude expansion bound: `‖u^t - 1‖ ≤ t ‖u - 1‖` for `u` in the closed unit disc. -/
theorem norm_pow_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1) (t : ℕ) : ‖u ^ t - 1‖ ≤ t * ‖u - 1‖ := by
  induction t with
  | zero => simp
  | succ n ih =>
      have e : u ^ (n + 1) - 1 = u ^ n * (u - 1) + (u ^ n - 1) := by ring
      rw [e]
      calc ‖u ^ n * (u - 1) + (u ^ n - 1)‖ ≤ ‖u ^ n * (u - 1)‖ + ‖u ^ n - 1‖ := norm_add_le _ _
        _ ≤ 1 * ‖u - 1‖ + n * ‖u - 1‖ := by
              gcongr
              · rw [norm_mul]
                gcongr
                simpa using pow_le_one₀ (norm_nonneg u) hu
        _ = ((n : ℝ) + 1) * ‖u - 1‖ := by ring
        _ = ((n + 1 : ℕ) : ℝ) * ‖u - 1‖ := by push_cast; ring

/-- Poincaré recurrence for a finite family of unimodular complex numbers: there is a positive
exponent `k` for which all the `k`-th powers are simultaneously within `ε` of `1`.

Proved by compactness of the closed unit polydisc. -/
theorem exists_pow_near_one_aux {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ k, 1 ≤ k ∧ ∀ i, ‖w i ^ k - 1‖ ≤ ε := by
  set F : ℕ → (ι → ℂ) := fun n i => w i ^ n with hF
  have hmem : ∀ n, F n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_
    intro i
    simp [hF, norm_pow, hw i]
  obtain ⟨a, -, psi, hpsi, hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hcauchy := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt : psi N < psi (N + 1) := hpsi (by omega)
  refine ⟨psi (N + 1) - psi N, by omega, ?_⟩
  intro i
  have hd : dist (F (psi (N + 1)) i) (F (psi N) i) < ε :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) (hN (N + 1) (by omega) N (by omega))
  have key : F (psi (N + 1)) i - F (psi N) i = w i ^ psi N * (w i ^ (psi (N + 1) - psi N) - 1) := by
    simp only [hF]
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  have hnorm : ‖F (psi (N + 1)) i - F (psi N) i‖ = ‖w i ^ (psi (N + 1) - psi N) - 1‖ := by
    rw [key, norm_mul, norm_pow, hw i, one_pow, one_mul]
  rw [dist_eq_norm, hnorm] at hd
  exact hd.le

/-- Recurrence with arbitrarily large exponents: for finitely many unimodular complex numbers
and any `ε > 0` and any bound `T`, there is `k ≥ T`, `k ≥ 1`, with all `w i ^ k` within `ε`
of `1`. -/
theorem exists_pow_near_one {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (T : ℕ) : ∃ k, T ≤ k ∧ 1 ≤ k ∧ ∀ i, ‖w i ^ k - 1‖ ≤ ε := by
  obtain ⟨k, hk1, hk⟩ := exists_pow_near_one_aux w hw (ε := ε / (T + 1)) (by positivity)
  refine ⟨(T + 1) * k, by nlinarith, by nlinarith, ?_⟩
  intro i
  have hu : ‖w i ^ k‖ ≤ 1 := by rw [norm_pow, hw i]; simp
  have h2 := norm_pow_sub_one_le hu (T + 1)
  rw [← pow_mul, mul_comm k (T + 1)] at h2
  calc ‖w i ^ ((T + 1) * k) - 1‖ ≤ ((T : ℝ) + 1) * ‖w i ^ k - 1‖ := by
        push_cast at h2 ⊢; linarith
    _ ≤ ((T : ℝ) + 1) * (ε / (T + 1)) := by gcongr; exact hk i
    _ = ε := by field_simp

/-! ### The Bombieri–Lagarias positivity theorem (finite case) -/

/-- **Bombieri–Lagarias, finite case.**  If the real parts of all the power sums
`∑ᵢ zᵢ ^ n` (`n ≥ 1`) of a finite family of complex numbers are bounded above by a constant,
then every member of the family lies in the closed unit disc. -/
theorem norm_le_one_of_re_sum_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ s, z i ^ n).re ≤ C) : ∀ i ∈ s, ‖z i‖ ≤ 1 := by
  intro i0 hi0
  by_contra hR
  push_neg at hR
  set R := ‖z i0‖ with hRdef
  have htend : Tendsto (fun k : ℕ => R ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hR
  obtain ⟨T, hT⟩ := (htend.eventually_gt_atTop (2 * C)).exists_forall_of_atTop
  set w : (↥s) → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ) with hwdef
  have hw : ∀ i : ↥s, ‖w i‖ = 1 := by
    intro i
    by_cases hz : z i = 0
    · simp [hwdef, hz]
    · simp [hwdef, hz]
  obtain ⟨k, hkT, hk1, hk⟩ := exists_pow_near_one w hw (ε := (1 : ℝ) / 2) (by norm_num) T
  have hterm : ∀ i ∈ s, ‖z i‖ ^ k / 2 ≤ (z i ^ k).re := by
    intro i hi
    by_cases hz : z i = 0
    · simp [hz, zero_pow (by omega : k ≠ 0)]
    · have hzn : (0 : ℝ) < ‖z i‖ := by simpa [norm_pos_iff] using hz
      have hsplit : z i = (‖z i‖ : ℂ) * w ⟨i, hi⟩ := by
        have hne : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
        simp only [hwdef, hz, if_false]
        field_simp
      have hre : (1 : ℝ) / 2 ≤ (w ⟨i, hi⟩ ^ k).re := by
        have h1 := hk ⟨i, hi⟩
        have h2 : (1 - w ⟨i, hi⟩ ^ k).re ≤ ‖1 - w ⟨i, hi⟩ ^ k‖ := Complex.re_le_norm _
        rw [norm_sub_rev] at h2
        simp only [Complex.sub_re, Complex.one_re] at h2
        linarith
      have hexp : (z i ^ k).re = ‖z i‖ ^ k * (w ⟨i, hi⟩ ^ k).re := by
        conv_lhs => rw [hsplit]
        rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
      rw [hexp]
      have hp : (0 : ℝ) ≤ ‖z i‖ ^ k := by positivity
      nlinarith
  have hsum : (∑ i ∈ s, z i ^ k).re = ∑ i ∈ s, (z i ^ k).re := by simp [Complex.re_sum]
  have h1 : R ^ k / 2 ≤ ∑ i ∈ s, (z i ^ k).re := by
    calc R ^ k / 2 ≤ ∑ i ∈ s, ‖z i‖ ^ k / 2 :=
          Finset.single_le_sum (f := fun i => ‖z i‖ ^ k / 2) (fun i _ => by positivity) hi0
      _ ≤ _ := Finset.sum_le_sum hterm
  have h2 := h k hk1
  rw [hsum] at h2
  have h3 := hT k hkT
  linarith

/-! ### Li's coefficients and Li's criterion -/

/-- The `n`-th **Li coefficient** of a finite family of "zeros" `ρ : ι → ℂ` indexed by a
`Finset s`:  `λ_n = Re ∑_ρ (1 - (1 - 1/ρ)^n)`. -/
noncomputable def liCoeff {ι : Type*} (s : Finset ι) (rho : ι → ℂ) (n : ℕ) : ℝ :=
  (∑ i ∈ s, (1 - (1 - 1 / rho i) ^ n)).re

/-- Rewriting of the Li coefficient in terms of the power sums of the Li transforms. -/
theorem liCoeff_eq {ι : Type*} (s : Finset ι) (rho : ι → ℂ) (n : ℕ) :
    liCoeff s rho n = s.card - (∑ i ∈ s, (1 - 1 / rho i) ^ n).re := by
  simp [liCoeff, Complex.re_sum, Finset.sum_sub_distrib]

/-- **Li's criterion (finite Bombieri–Lagarias form).**

Let `ρ : ι → ℂ` be a family of nonzero complex numbers indexed by a finite set `s`
(multiplicities allowed, since the indexing is by an arbitrary finite index set), and assume the
family is closed under the functional-equation symmetry `ρ ↦ 1 - ρ`.  Then the "Riemann
Hypothesis" for this family — all the `ρ i` lie on the critical line `Re ρ = 1/2` — holds if and
only if all the Li coefficients `λ_n`, `n ≥ 1`, are nonnegative. -/
theorem RH_Li_criterion {ι : Type*} (s : Finset ι) (rho : ι → ℂ)
    (h0 : ∀ i ∈ s, rho i ≠ 0)
    (hsym : ∀ i ∈ s, ∃ j ∈ s, rho j = 1 - rho i) :
    (∀ i ∈ s, (rho i).re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff s rho n := by
  constructor
  · -- Easy direction: on the critical line, `|1 - 1/ρ| ≤ 1`, so every summand has
    -- nonnegative real part.
    intro hcrit n _
    rw [liCoeff, Complex.re_sum]
    refine Finset.sum_nonneg ?_
    intro i hi
    have hdisc : ‖1 - 1 / rho i‖ ≤ 1 :=
      (norm_one_sub_inv_le_one_iff (h0 i hi)).2 (le_of_eq (hcrit i hi).symm)
    have hpow : ‖(1 - 1 / rho i) ^ n‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hdisc
    have := Complex.re_le_norm ((1 - 1 / rho i) ^ n)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · -- Hard direction: bounded power sums force all Li transforms into the closed unit disc,
    -- i.e. `Re ρ ≥ 1/2`; the symmetry `ρ ↦ 1 - ρ` then pins them to the critical line.
    intro hpos
    have hbound : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ s, (1 - 1 / rho i) ^ n).re ≤ (s.card : ℝ) := by
      intro n hn
      have := hpos n hn
      rw [liCoeff_eq] at this
      linarith
    have hdisc := norm_le_one_of_re_sum_pow_le s (fun i => 1 - 1 / rho i) (s.card : ℝ) hbound
    have hhalf : ∀ i ∈ s, 1 / 2 ≤ (rho i).re := fun i hi =>
      (norm_one_sub_inv_le_one_iff (h0 i hi)).1 (hdisc i hi)
    intro i hi
    obtain ⟨j, hj, hji⟩ := hsym i hi
    have h1 := hhalf i hi
    have h2 := hhalf j hj
    rw [hji] at h2
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith

/-! ### Non-vacuity checks

The hypotheses of `RH_Li_criterion` are satisfiable by nonempty families, on and off the
critical line. -/

/-- A two-element family on the critical line, closed under `ρ ↦ 1 - ρ`: all its Li
coefficients are nonnegative. -/
example : ∀ n : ℕ, 1 ≤ n →
    0 ≤ liCoeff (Finset.univ : Finset (Fin 2)) ![(1 : ℂ) / 2 + Complex.I, 1 / 2 - Complex.I] n := by
  refine (RH_Li_criterion _ _ ?_ ?_).1 ?_
  · intro i _
    fin_cases i <;> simp [Complex.ext_iff]
  · intro i _
    fin_cases i
    · exact ⟨1, Finset.mem_univ _, by simp; ring⟩
    · exact ⟨0, Finset.mem_univ _, by simp; ring⟩
  · intro i _
    fin_cases i <;> simp

/-- A two-element family off the critical line, closed under `ρ ↦ 1 - ρ`: some Li coefficient
is negative. -/
example : ∃ n : ℕ, 1 ≤ n ∧
    liCoeff (Finset.univ : Finset (Fin 2)) ![(1 : ℂ) / 4, 3 / 4] n < 0 := by
  have h := (RH_Li_criterion (Finset.univ : Finset (Fin 2)) ![(1 : ℂ) / 4, 3 / 4] ?_ ?_).not
  · have hnot : ¬ ∀ i ∈ (Finset.univ : Finset (Fin 2)), (![(1 : ℂ) / 4, 3 / 4] i).re = 1 / 2 := by
      intro hc
      have := hc 0 (Finset.mem_univ _)
      norm_num at this
    have := h.1 hnot
    push_neg at this
    obtain ⟨n, hn, hlt⟩ := this
    exact ⟨n, hn, hlt⟩
  · intro i _
    fin_cases i <;> simp
  · intro i _
    fin_cases i
    · exact ⟨1, Finset.mem_univ _, by norm_num⟩
    · exact ⟨0, Finset.mem_univ _, by norm_num⟩

end Frontier

