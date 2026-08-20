/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `QI.log_sum_le`, `QI.klDiv_stochastic_le`, `QI.classical_holevo`: the classical core, namely the
  log-sum inequality, the data-processing inequality for the Kullback–Leibler divergence, and the
  resulting data-processing inequality for mutual information.
* `QI.vonNeumannEntropy`, `QI.IsState`, `QI.IsPOVM`, `QI.outcomeProb`, `QI.holevoChi`,
  `QI.measuredInfo`, `QI.accessibleInfo`: the quantum-information definitions.
* `QI.holevo_bound`: for an ensemble of density matrices measured by an arbitrary POVM, the
  mutual information between the ensemble label and the measurement outcome is at most the
  Holevo quantity `χ`.
* `QI.accessibleInfo_le_holevoChi`: the same statement for the supremum over POVMs.

## Scope

The ensemble is assumed to consist of *commuting* density matrices: they are given as
`ρ x = U * diagonal (r x) * Uᴴ` for one fixed unitary `U` and probability vectors `r x`.  The
measurement, on the other hand, is a completely arbitrary POVM, so the argument is not a purely
classical one: the POVM has to be turned into a stochastic matrix via `i ↦ (Uᴴ (E y) U) i i`.
The fully general (non-commuting) Holevo bound needs monotonicity of the *quantum* relative
entropy under measurement, which is not available in Mathlib.
-/

open Finset

namespace QI

/-! ## Classical information-theoretic core -/

/-- Shannon entropy of a finite (sub)probability vector, with the convention `0 * log 0 = 0`. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (a i)

/-- Kullback–Leibler divergence of two finite (sub)probability vectors. -/
noncomputable def klDiv {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  ∑ i, a i * (Real.log (a i) - Real.log (b i))

/-- The log-sum inequality. -/
theorem log_sum_le {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hac : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * (Real.log (∑ i, a i) - Real.log (∑ i, b i)) ≤ klDiv a b := by
  have hB0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  rcases hB0.eq_or_lt with hBz | hBpos
  · have hbz : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hb j)).1 hBz.symm i (mem_univ i)
    have haz : ∀ i, a i = 0 := fun i => hac i (hbz i)
    simp [klDiv, haz, hbz]
  · have hbpos : ∀ i, 0 < a i → 0 < b i := by
      intro i hai
      rcases (hb i).eq_or_lt with h | h
      · exact absurd (hac i h.symm) (ne_of_gt hai)
      · exact h
    have key : ∀ i ∈ (univ : Finset ι),
        a i - b i * ((∑ j, a j) / (∑ j, b j))
          ≤ a i * (Real.log (a i) - Real.log (b i))
            - a i * (Real.log (∑ j, a j) - Real.log (∑ j, b j)) := by
      intro i _
      rcases (ha i).eq_or_lt with hai | hai
      · have : 0 ≤ b i * ((∑ j, a j) / (∑ j, b j)) :=
          mul_nonneg (hb i) (div_nonneg (Finset.sum_nonneg fun j _ => ha j) hB0)
        simp only [← hai]
        linarith
      · have hApos : 0 < ∑ j, a j :=
          lt_of_lt_of_le hai (Finset.single_le_sum (fun j _ => ha j) (mem_univ i))
        have hbi := hbpos i hai
        have ht : 0 < (b i * (∑ j, a j)) / (a i * (∑ j, b j)) := by positivity
        have hlog := Real.log_le_sub_one_of_pos ht
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (ne_of_gt hbi) (ne_of_gt hApos),
          Real.log_mul (ne_of_gt hai) (ne_of_gt hBpos)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hai)
        have hsimp : a i * ((b i * (∑ j, a j)) / (a i * (∑ j, b j)) - 1)
            = b i * ((∑ j, a j) / (∑ j, b j)) - a i := by
          field_simp
        rw [hsimp] at hmul
        nlinarith [hmul]
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
    have hzero : (∑ j, b j) * ((∑ j, a j) / (∑ j, b j)) = ∑ j, a j := by
      field_simp
    rw [hzero] at hsum
    simpa [klDiv] using hsum

/-- Data-processing inequality for the KL divergence under a stochastic map. -/
theorem klDiv_stochastic_le {ι κ : Type*} [Fintype ι] [Fintype κ] (T : ι → κ → ℝ)
    (hT0 : ∀ i k, 0 ≤ T i k) (hT1 : ∀ i, ∑ k, T i k = 1)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hac : ∀ i, b i = 0 → a i = 0) :
    klDiv (fun k => ∑ i, a i * T i k) (fun k => ∑ i, b i * T i k) ≤ klDiv a b := by
  have hterm : ∀ i k, (a i * T i k) * (Real.log (a i * T i k) - Real.log (b i * T i k))
      = T i k * (a i * (Real.log (a i) - Real.log (b i))) := by
    intro i k
    rcases (hT0 i k).eq_or_lt with hTk | hTk
    · simp [← hTk]
    rcases (ha i).eq_or_lt with hai | hai
    · simp [← hai]
    · have hbi : 0 < b i := by
        rcases (hb i).eq_or_lt with h | h
        · exact absurd (hac i h.symm) (ne_of_gt hai)
        · exact h
      rw [Real.log_mul (ne_of_gt hai) (ne_of_gt hTk), Real.log_mul (ne_of_gt hbi) (ne_of_gt hTk)]
      ring
  have h1 : klDiv a b = ∑ k, klDiv (fun i => a i * T i k) (fun i => b i * T i k) := by
    simp only [klDiv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hterm i]
    rw [← Finset.sum_mul, hT1 i, one_mul]
  rw [h1, klDiv]
  refine Finset.sum_le_sum fun k _ => ?_
  refine log_sum_le (fun i => a i * T i k) (fun i => b i * T i k)
    (fun i => mul_nonneg (ha i) (hT0 i k)) (fun i => mul_nonneg (hb i) (hT0 i k)) ?_
  intro i hi
  dsimp only at hi ⊢
  rcases mul_eq_zero.1 hi with h | h
  · rw [hac i h]; ring
  · rw [h]; ring

/-- The mutual information of a classical ensemble, written with KL divergences. -/
theorem sum_klDiv_eq {X ι : Type*} [Fintype X] [Fintype ι] (p : X → ℝ) (r : X → ι → ℝ) :
    ∑ x, p x * klDiv (r x) (fun i => ∑ x', p x' * r x' i)
      = shannonEntropy (fun i => ∑ x', p x' * r x' i) - ∑ x, p x * shannonEntropy (r x) := by
  have step : ∀ x, p x * klDiv (r x) (fun i => ∑ x', p x' * r x' i) + p x * shannonEntropy (r x)
      = ∑ i, -(p x * r x i * Real.log (∑ x', p x' * r x' i)) := by
    intro x
    simp only [klDiv, shannonEntropy, Real.negMulLog, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : ∑ x, (p x * klDiv (r x) (fun i => ∑ x', p x' * r x' i) + p x * shannonEntropy (r x))
      = shannonEntropy (fun i => ∑ x', p x' * r x' i) := by
    simp only [step]
    rw [Finset.sum_comm]
    simp only [shannonEntropy, Real.negMulLog]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_add_distrib] at key
  linarith

/-- Classical data-processing inequality for mutual information. -/
theorem classical_holevo {X ι κ : Type*} [Fintype X] [Fintype ι] [Fintype κ]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (r : X → ι → ℝ) (hr0 : ∀ x i, 0 ≤ r x i)
    (T : ι → κ → ℝ) (hT0 : ∀ i k, 0 ≤ T i k) (hT1 : ∀ i, ∑ k, T i k = 1) :
    shannonEntropy (fun k => ∑ x, p x * ∑ i, r x i * T i k)
        - ∑ x, p x * shannonEntropy (fun k => ∑ i, r x i * T i k)
      ≤ shannonEntropy (fun i => ∑ x, p x * r x i) - ∑ x, p x * shannonEntropy (r x) := by
  have hqb : ∀ k, (∑ x, p x * ∑ i, r x i * T i k) = ∑ i, (∑ x, p x * r x i) * T i k := by
    intro k
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  have hL := sum_klDiv_eq p (fun x k => ∑ i, r x i * T i k)
  have hR := sum_klDiv_eq p r
  rw [← hL, ← hR]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases (hp0 x).eq_or_lt with hpx | hpx
  · simp [← hpx]
  · refine mul_le_mul_of_nonneg_left ?_ (hp0 x)
    have hac : ∀ i, (∑ x', p x' * r x' i) = 0 → r x i = 0 := by
      intro i hi
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x' _ => mul_nonneg (hp0 x') (hr0 x' i))).1 hi x (mem_univ x)
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (ne_of_gt hpx)
      · exact h
    have hdpi := klDiv_stochastic_le T hT0 hT1 (r x) (fun i => ∑ x', p x' * r x' i)
      (hr0 x) (fun i => Finset.sum_nonneg fun x' _ => mul_nonneg (hp0 x') (hr0 x' i)) hac
    simpa only [hqb] using hdpi

/-! ## Quantum setting -/

open Matrix Polynomial
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix: positive semidefinite with unit trace. -/
def IsState (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- A POVM: a family of positive semidefinite operators summing to the identity. -/
def IsPOVM {Y : Type*} [Fintype Y] (E : Y → Matrix n n ℂ) : Prop :=
  (∀ y, (E y).PosSemidef) ∧ ∑ y, E y = 1

/-- The von Neumann entropy of a state, i.e. the Shannon entropy of its spectrum. -/
noncomputable def vonNeumannEntropy (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

/-- The Born-rule probability of outcome `F` in the state `ρ`. -/
noncomputable def outcomeProb (ρ F : Matrix n n ℂ) : ℝ := (ρ * F).trace.re

/-- The Holevo quantity `χ` of the ensemble `{p x, ρ x}`. -/
noncomputable def holevoChi {X : Type*} [Fintype X] (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x) - ∑ x, p x * vonNeumannEntropy (ρ x)

/-- The classical mutual information between the ensemble label and the outcome of the
measurement `E`. The accessible information is the supremum of this over all POVMs `E`. -/
noncomputable def measuredInfo {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (ρ : X → Matrix n n ℂ) (E : Y → Matrix n n ℂ) : ℝ :=
  shannonEntropy (fun y => ∑ x, p x * outcomeProb (ρ x) (E y))
    - ∑ x, p x * shannonEntropy (fun y => outcomeProb (ρ x) (E y))

/-- Two families of scalars with the same monic split characteristic polynomial agree up to
permutation. -/
theorem multiset_map_eq_of_prod_X_sub_C_eq {ι : Type*} [Fintype ι] (f g : ι → ℂ)
    (h : ∏ i, (X - C (f i)) = ∏ i, (X - C (g i))) :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val := by
  have hf : ∀ (u : ι → ℂ), (∏ i, (X - C (u i)))
      = (Multiset.map (fun a => X - C a) (Multiset.map u Finset.univ.val)).prod := by
    intro u; rw [Multiset.map_map]; rfl
  rw [hf f, hf g] at h
  have h2 := congrArg Polynomial.roots h
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h2

/-- A unitary conjugate of a real diagonal matrix is Hermitian. -/
theorem isHermitian_unitary_conj_diagonal (U : Matrix n n ℂ) (v : n → ℝ) :
    (U * diagonal (fun i => (v i : ℂ)) * Uᴴ).IsHermitian := by
  have hD : (diagonal (fun i => (v i : ℂ)))ᴴ = diagonal (fun i => (v i : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  unfold Matrix.IsHermitian
  simp [Matrix.conjTranspose_mul, mul_assoc, hD]

/-- The von Neumann entropy of `U * diag v * Uᴴ` is the Shannon entropy of `v`. -/
theorem vonNeumannEntropy_unitary_conj_diagonal {U : Matrix n n ℂ} (hU1 : Uᴴ * U = 1) (v : n → ℝ) :
    vonNeumannEntropy (U * diagonal (fun i => (v i : ℂ)) * Uᴴ) = shannonEntropy v := by
  have hH := isHermitian_unitary_conj_diagonal U v
  rw [vonNeumannEntropy, dif_pos hH, shannonEntropy]
  have hchar : (U * diagonal (fun i => (v i : ℂ)) * Uᴴ).charpoly
      = (diagonal (fun i => (v i : ℂ))).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hU1, one_mul]
  have h1 := hH.charpoly_eq
  rw [hchar, Matrix.charpoly_diagonal] at h1
  have hms := multiset_map_eq_of_prod_X_sub_C_eq _ _ h1
  have h2 := congrArg (Multiset.map (fun z : ℂ => Real.negMulLog z.re)) hms
  rw [Multiset.map_map, Multiset.map_map] at h2
  have h3 := congrArg Multiset.sum h2
  simpa [Function.comp] using h3.symm

/-- Born probabilities for a unitarily-diagonalized state. -/
theorem outcomeProb_unitary_conj_diagonal (U : Matrix n n ℂ) (v : n → ℝ) (F : Matrix n n ℂ) :
    outcomeProb (U * diagonal (fun i => (v i : ℂ)) * Uᴴ) F
      = ∑ i, v i * ((Uᴴ * F * U) i i).re := by
  have h1 : (U * diagonal (fun i => (v i : ℂ)) * Uᴴ * F).trace
      = (diagonal (fun i => (v i : ℂ)) * (Uᴴ * F * U)).trace := by
    rw [show U * diagonal (fun i => (v i : ℂ)) * Uᴴ * F
        = U * (diagonal (fun i => (v i : ℂ)) * (Uᴴ * F)) from by noncomm_ring,
      Matrix.trace_mul_comm, mul_assoc]
  rw [outcomeProb, h1]
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum, Complex.mul_re]

/-- Averaging commutes with unitary conjugation of diagonal matrices. -/
theorem sum_smul_unitary_conj_diagonal {X : Type*} [Fintype X] (U : Matrix n n ℂ)
    (p : X → ℝ) (r : X → n → ℝ) :
    ∑ x, (p x : ℂ) • (U * diagonal (fun i => (r x i : ℂ)) * Uᴴ)
      = U * diagonal (fun i => ((∑ x, p x * r x i : ℝ) : ℂ)) * Uᴴ := by
  have h1 : ∀ x, (p x : ℂ) • (U * diagonal (fun i => (r x i : ℂ)) * Uᴴ)
      = U * ((p x : ℂ) • diagonal (fun i => (r x i : ℂ))) * Uᴴ := by
    intro x; simp
  simp only [h1]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, hij]

/-- `U * diag v * Uᴴ` really is a density matrix when `v` is a probability vector. -/
theorem isState_unitary_conj_diagonal (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (v : n → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i = 1) :
    IsState (U * diagonal (fun i => (v i : ℂ)) * Uᴴ) := by
  constructor
  · have hd : (diagonal (fun i => (v i : ℂ))).PosSemidef :=
      Matrix.PosSemidef.diagonal (Pi.le_def.mpr fun i =>
        Complex.le_def.mpr ⟨by simpa using hv0 i, by simp⟩)
    simpa using hd.mul_mul_conjTranspose_same U
  · rw [Matrix.trace_mul_comm, ← mul_assoc, hU1, one_mul, Matrix.trace_diagonal,
      ← Complex.ofReal_sum, hv1, Complex.ofReal_one]

/-- The diagonal of `Uᴴ * E y * U` gives a stochastic matrix. -/
theorem povm_stochastic_nonneg {Y : Type*} [Fintype Y] (U : Matrix n n ℂ)
    {E : Y → Matrix n n ℂ} (hE : IsPOVM E) (i : n) (y : Y) :
    0 ≤ ((Uᴴ * E y * U) i i).re := by
  have h : (Uᴴ * E y * U).PosSemidef := by
    simpa using (hE.1 y).mul_mul_conjTranspose_same Uᴴ
  simpa using (Complex.le_def.mp h.diag_nonneg).1

theorem povm_stochastic_sum {Y : Type*} [Fintype Y] {U : Matrix n n ℂ} (hU1 : Uᴴ * U = 1)
    {E : Y → Matrix n n ℂ} (hE : IsPOVM E) (i : n) :
    ∑ y, ((Uᴴ * E y * U) i i).re = 1 := by
  have hsum : ∑ y, (Uᴴ * E y * U) i i = (1 : Matrix n n ℂ) i i := by
    have : ∑ y, Uᴴ * E y * U = (1 : Matrix n n ℂ) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE.2, mul_one, hU1]
    calc ∑ y, (Uᴴ * E y * U) i i = (∑ y, Uᴴ * E y * U) i i := (Matrix.sum_apply i i _ _).symm
      _ = (1 : Matrix n n ℂ) i i := by rw [this]
  rw [← Complex.re_sum, hsum]
  simp

/-- **The Holevo bound.**

Let `{p x, ρ x}` be an ensemble of density matrices on a finite-dimensional Hilbert space that
are simultaneously diagonalized by a unitary `U`, with spectra `r x`, and let `E` be an
arbitrary POVM.  Then the classical mutual information between the ensemble label and the
measurement outcome is at most the Holevo quantity
`χ = S(∑ x p x ρ x) - ∑ x p x S(ρ x)`.  Since this holds for every POVM `E`, the accessible
information (the supremum over POVMs) is at most `χ`.

The normalization hypotheses `hp1` and `hr1` say that `p` is a probability distribution and each
`ρ x` is a genuine density matrix (see `QI.isState_unitary_conj_diagonal`); they are recorded for
faithfulness even though the inequality itself does not need them. -/
theorem holevo_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → n → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, ρ x = U * diagonal (fun i => (r x i : ℂ)) * Uᴴ)
    (E : Y → Matrix n n ℂ) (hE : IsPOVM E) :
    measuredInfo p ρ E ≤ holevoChi p ρ := by
  have hop : ∀ x y, outcomeProb (ρ x) (E y) = ∑ i, r x i * ((Uᴴ * E y * U) i i).re := by
    intro x y; rw [hρ x, outcomeProb_unitary_conj_diagonal]
  have hvn : ∀ x, vonNeumannEntropy (ρ x) = shannonEntropy (r x) := by
    intro x; rw [hρ x, vonNeumannEntropy_unitary_conj_diagonal hU1]
  have havg : vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x)
      = shannonEntropy (fun i => ∑ x, p x * r x i) := by
    simp only [hρ]
    rw [sum_smul_unitary_conj_diagonal, vonNeumannEntropy_unitary_conj_diagonal hU1]
  rw [measuredInfo, holevoChi, havg]
  simp only [hop, hvn]
  exact classical_holevo p hp0 r hr0 (fun i y => ((Uᴴ * E y * U) i i).re)
    (fun i y => povm_stochastic_nonneg U hE i y) (povm_stochastic_sum hU1 hE)

/-- The Holevo quantity of an ensemble is nonnegative. -/
theorem holevoChi_nonneg {X : Type*} [Fintype X]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → n → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, ρ x = U * diagonal (fun i => (r x i : ℂ)) * Uᴴ) :
    0 ≤ holevoChi p ρ := by
  have hvn : ∀ x, vonNeumannEntropy (ρ x) = shannonEntropy (r x) := by
    intro x; rw [hρ x, vonNeumannEntropy_unitary_conj_diagonal hU1]
  have havg : vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x)
      = shannonEntropy (fun i => ∑ x, p x * r x i) := by
    simp only [hρ]
    rw [sum_smul_unitary_conj_diagonal, vonNeumannEntropy_unitary_conj_diagonal hU1]
  have hrb0 : ∀ i, 0 ≤ ∑ x, p x * r x i :=
    fun i => Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hr0 x i)
  have hrb1 : ∑ i, (∑ x, p x * r x i) = 1 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hr1, mul_one]
    exact hp1
  rw [holevoChi, havg]
  simp only [hvn]
  rw [← sum_klDiv_eq p r]
  refine Finset.sum_nonneg fun x _ => ?_
  rcases (hp0 x).eq_or_lt with hpx | hpx
  · simp [← hpx]
  refine mul_nonneg (hp0 x) ?_
  have hac : ∀ i, (∑ x', p x' * r x' i) = 0 → r x i = 0 := by
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x' _ => mul_nonneg (hp0 x') (hr0 x' i))).1 hi x (mem_univ x)
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (ne_of_gt hpx)
    · exact h
  have hls := log_sum_le (r x) (fun i => ∑ x', p x' * r x' i) (hr0 x) hrb0 hac
  rwa [hr1 x, hrb1, Real.log_one, sub_self, mul_zero] at hls

/-- The accessible information of an ensemble, i.e. the supremum over all POVMs with outcome
set `Y` of the mutual information between the ensemble label and the measurement outcome. -/
noncomputable def accessibleInfo {X : Type*} (Y : Type*) [Fintype X] [Fintype Y]
    (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  ⨆ E : {E : Y → Matrix n n ℂ // IsPOVM E}, measuredInfo p ρ E.1

/-- **Accessible information is at most the Holevo `χ` quantity.** -/
theorem accessibleInfo_le_holevoChi {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → n → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix n n ℂ) (hU1 : Uᴴ * U = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, ρ x = U * diagonal (fun i => (r x i : ℂ)) * Uᴴ) :
    accessibleInfo Y p ρ ≤ holevoChi p ρ :=
  Real.iSup_le (fun E => holevo_bound p hp0 hp1 r hr0 hr1 U hU1 ρ hρ E.1 E.2)
    (holevoChi_nonneg p hp0 hp1 r hr0 hr1 U hU1 ρ hρ)

end QI

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

