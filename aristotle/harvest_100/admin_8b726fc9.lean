import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope and contents

States are density matrices `ρ : Matrix d d ℂ`, measurements are POVMs (`QI.IsPOVM`), the von
Neumann entropy `QI.vonNeumannEntropy` is the sum of `-λ log λ` over the eigenvalues, and
`QI.holevoChi` is `S(∑ pₓ ρₓ) - ∑ pₓ S(ρₓ)`.

The main theorem `QI.holevo_bound` proves the Holevo bound
`I(X;Y) ≤ χ` for ensembles of *commuting* states, i.e. states that are simultaneously
diagonalizable by one unitary `U`, and for an arbitrary POVM measurement; the supremum form
`QI.accessibleInfo_le_holevoChi` then bounds the accessible information by `χ`.
The general (non-commuting) case rests on the monotonicity of quantum relative entropy, which
is not available in Mathlib and is not developed here.

The mathematical core is classical: the log-sum inequality (`QI.log_sum_inequality`) and the
resulting data-processing inequality for the Kullback-Leibler divergence
(`QI.kl_data_processing`); the Holevo quantity of a commuting ensemble is
`∑ₓ pₓ D(rₓ ‖ r̄)`, and measuring with a POVM applies the stochastic map
`W y i = (E y) i i` to each `rₓ`.
-/

namespace QI

open Matrix Real Finset ComplexOrder

/-! ## Classical information-theoretic core -/

/-- The log-sum inequality:
`(∑ aᵢ) log ((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ log (aᵢ/bᵢ)` for nonnegative `a`, `b` with `a ≪ b`. -/
theorem log_sum_inequality {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hB0 with hB' | hB'
  · have hbz : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 hB'.symm i (mem_univ i)
    have haz : ∀ i, a i = 0 := fun i => hab i (hbz i)
    have hAz : A = 0 := by simp [hA, haz]
    simp [hAz, haz]
  · rcases eq_or_lt_of_le hA0 with hA' | hA'
    · have haz : ∀ i, a i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hA'.symm i (mem_univ i)
      simp [← hA', haz]
    · have key : ∀ i ∈ (univ : Finset ι),
          a i * Real.log (A / B) + (a i - b i * (A / B)) ≤ a i * Real.log (a i / b i) := by
        intro i _
        rcases eq_or_lt_of_le (ha i) with hai | hai
        · have h0 : a i = 0 := hai.symm
          simp only [h0, zero_mul, zero_sub, zero_add]
          have : 0 ≤ b i * (A / B) := mul_nonneg (hb i) (by positivity)
          linarith
        · have hbi : 0 < b i := by
            rcases eq_or_lt_of_le (hb i) with h | h
            · exact absurd (hab i h.symm) (by linarith)
            · exact h
          have htpos : 0 < (a i / b i) / (A / B) := by positivity
          set t := (a i / b i) / (A / B) with ht
          have hlogt : Real.log t = Real.log (a i / b i) - Real.log (A / B) := by
            rw [ht, Real.log_div (by positivity) (by positivity)]
          have h1 : 1 - t⁻¹ ≤ Real.log t := by
            have := Real.log_le_sub_one_of_pos (show (0:ℝ) < t⁻¹ by positivity)
            rw [Real.log_inv] at this
            linarith
          have h2 : a i * t⁻¹ = b i * (A / B) := by rw [ht]; field_simp
          have h3 := mul_le_mul_of_nonneg_left h1 hai.le
          have h4 : a i * (1 - t⁻¹) = a i - b i * (A / B) := by rw [mul_sub, mul_one, h2]
          have h5 : a i * Real.log t = a i * Real.log (a i / b i) - a i * Real.log (A / B) := by
            rw [hlogt]; ring
          linarith
      have hsum := Finset.sum_le_sum key
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
        ← Finset.sum_mul] at hsum
      rw [← hA, ← hB] at hsum
      have hBA : B * (A / B) = A := by field_simp
      rw [hBA] at hsum
      simpa using hsum

/-- Data processing inequality for the Kullback-Leibler divergence:
applying a stochastic map `W` to two distributions cannot increase their divergence. -/
theorem kl_data_processing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : κ → ι → ℝ) (hW0 : ∀ y i, 0 ≤ W y i) (hW1 : ∀ i, ∑ y, W y i = 1)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    ∑ y, (∑ i, W y i * a i) * Real.log ((∑ i, W y i * a i) / (∑ i, W y i * b i))
      ≤ ∑ i, a i * Real.log (a i / b i) := by
  have step : ∀ y ∈ (univ : Finset κ),
      (∑ i, W y i * a i) * Real.log ((∑ i, W y i * a i) / (∑ i, W y i * b i))
        ≤ ∑ i, W y i * (a i * Real.log (a i / b i)) := by
    intro y _
    have h := log_sum_inequality (fun i => W y i * a i) (fun i => W y i * b i)
      (fun i => mul_nonneg (hW0 y i) (ha i)) (fun i => mul_nonneg (hW0 y i) (hb i))
      (by
        intro i hi
        rcases mul_eq_zero.1 hi with h | h
        · simp [h]
        · simp [hab i h])
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hw : W y i = 0
    · simp [hw]
    · rw [mul_div_mul_left _ _ hw, mul_assoc]
  calc ∑ y, (∑ i, W y i * a i) * Real.log ((∑ i, W y i * a i) / (∑ i, W y i * b i))
      ≤ ∑ y, ∑ i, W y i * (a i * Real.log (a i / b i)) := Finset.sum_le_sum step
    _ = ∑ i, (∑ y, W y i) * (a i * Real.log (a i / b i)) := by
        rw [Finset.sum_comm]; simp [Finset.sum_mul]
    _ = ∑ i, a i * Real.log (a i / b i) := by simp [hW1]

/-! ## Quantum definitions -/

variable {d X Y : Type*}

open Classical in
/-- The von Neumann entropy `S(ρ) = -Tr ρ log ρ` of a Hermitian matrix, computed from its
eigenvalues. (It is set to `0` on non-Hermitian matrices.) -/
noncomputable def vonNeumannEntropy [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

/-- A POVM: a finite family of positive semidefinite matrices summing to the identity. -/
def IsPOVM [Fintype Y] [DecidableEq d] (E : Y → Matrix d d ℂ) : Prop :=
  (∀ y, (E y).PosSemidef) ∧ ∑ y, E y = 1

/-- The Born-rule probability `Tr (E ρ)` of the outcome associated with the POVM element `E`
when measuring the state `ρ`. -/
noncomputable def outcomeProb [Fintype d] (E ρ : Matrix d d ℂ) : ℝ := ((E * ρ).trace).re

/-- The classical mutual information `I(X;Y)` of the joint distribution
`P(x,y) = p x * Tr (E y * ρ x)` obtained by measuring the ensemble `(p, ρ)` with the POVM `E`. -/
noncomputable def measuredInfo [Fintype d] [Fintype X] [Fintype Y]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (E : Y → Matrix d d ℂ) : ℝ :=
  ∑ x, ∑ y, p x * outcomeProb (E y) (ρ x) *
    Real.log (outcomeProb (E y) (ρ x) / ∑ x', p x' * outcomeProb (E y) (ρ x'))

/-- The accessible information of the ensemble `(p, ρ)` for measurements with outcome set `O`:
the supremum of the measured mutual information over all POVMs indexed by `O`. -/
noncomputable def accessibleInfo [Fintype d] [DecidableEq d] [Fintype X] (O : Type*) [Fintype O]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) : ℝ :=
  sSup {I : ℝ | ∃ E : O → Matrix d d ℂ, IsPOVM E ∧ I = measuredInfo p ρ E}

/-- The Holevo quantity `χ = S(∑ pₓ ρₓ) - ∑ pₓ S(ρₓ)` of an ensemble. -/
noncomputable def holevoChi [Fintype d] [DecidableEq d] [Fintype X]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) : ℝ :=
  vonNeumannEntropy (∑ x, p x • ρ x) - ∑ x, p x * vonNeumannEntropy (ρ x)

/-! ## Basic facts about the definitions -/

/-- Unfolding of `vonNeumannEntropy` for a Hermitian matrix. -/
theorem vonNeumannEntropy_of_isHermitian [Fintype d] [DecidableEq d] {ρ : Matrix d d ℂ}
    (h : ρ.IsHermitian) : vonNeumannEntropy ρ = ∑ i, Real.negMulLog (h.eigenvalues i) := by
  rw [vonNeumannEntropy, dif_pos h]

/-- Conjugating a Hermitian matrix keeps it Hermitian. -/
theorem isHermitian_conj [Fintype d] [DecidableEq d] (V : Matrix d d ℂ)
    {σ : Matrix d d ℂ} (h : σ.IsHermitian) : (V * σ * star V).IsHermitian := by
  rw [Matrix.star_eq_conjTranspose]
  simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, h.eq, Matrix.mul_assoc]

/-- A real diagonal matrix is Hermitian. -/
theorem isHermitian_diagonal_real [Fintype d] [DecidableEq d] (v : d → ℝ) :
    (Matrix.diagonal fun i => (v i : ℂ)).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint, Complex.conj_ofReal]

/-- The von Neumann entropy of a real diagonal matrix is the Shannon entropy of its diagonal. -/
theorem vonNeumannEntropy_diagonal [Fintype d] [DecidableEq d] (v : d → ℝ) :
    vonNeumannEntropy (Matrix.diagonal fun i => (v i : ℂ)) = ∑ i, Real.negMulLog (v i) := by
  have h := isHermitian_diagonal_real v
  rw [vonNeumannEntropy_of_isHermitian h]
  have hroots : (Matrix.diagonal fun i => (v i : ℂ)).charpoly.roots
      = Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod]
    rw [show (Multiset.map (fun i => Polynomial.X - Polynomial.C ((v i : ℂ))) Finset.univ.val)
        = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
          (Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [h.roots_charpoly_eq_eigenvalues] at hroots
  have hm : Multiset.map h.eigenvalues Finset.univ.val = Multiset.map v Finset.univ.val := by
    refine Multiset.map_injective Complex.ofReal_injective ?_
    rw [Multiset.map_map, Multiset.map_map]
    exact hroots
  have e1 : ∑ i, Real.negMulLog (h.eigenvalues i)
      = (Multiset.map Real.negMulLog (Multiset.map h.eigenvalues Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  have e2 : ∑ i, Real.negMulLog (v i)
      = (Multiset.map Real.negMulLog (Multiset.map v Finset.univ.val)).sum := by
    rw [Multiset.map_map]; rfl
  rw [e1, e2, hm]

/-- The von Neumann entropy is invariant under unitary conjugation. -/
theorem vonNeumannEntropy_unitary_conj [Fintype d] [DecidableEq d] {U : Matrix d d ℂ}
    (hU : U ∈ Matrix.unitaryGroup d ℂ) (ρ : Matrix d d ℂ) :
    vonNeumannEntropy (U * ρ * star U) = vonNeumannEntropy ρ := by
  have h1 : star U * U = 1 := hU.1
  have h2 : U * star U = 1 := hU.2
  have hback : star U * (U * ρ * star U) * U = ρ := by
    calc star U * (U * ρ * star U) * U = (star U * U) * ρ * (star U * U) := by
          simp [Matrix.mul_assoc]
      _ = ρ := by rw [h1]; simp
  by_cases h : ρ.IsHermitian
  · have h' : (U * ρ * star U).IsHermitian := isHermitian_conj U h
    rw [vonNeumannEntropy_of_isHermitian h', vonNeumannEntropy_of_isHermitian h]
    have hchar : (U * ρ * star U).charpoly = ρ.charpoly := by
      let u : (Matrix d d ℂ)ˣ := ⟨U, star U, h2, h1⟩
      have h3 : ((u : (Matrix d d ℂ)ˣ) : Matrix d d ℂ) * ρ *
          ((u⁻¹ : (Matrix d d ℂ)ˣ) : Matrix d d ℂ) = U * ρ * star U := by
        simp [u, Units.inv_mk]
      have := Matrix.charpoly_units_conj u ρ
      rwa [h3] at this
    rw [(Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff h' h).2 hchar]
  · have h' : ¬ (U * ρ * star U).IsHermitian := by
      intro hc
      have := isHermitian_conj (star U) hc
      rw [star_star, hback] at this
      exact h this
    simp only [vonNeumannEntropy, dif_neg h, dif_neg h']

/-- Born probabilities for a diagonal state. -/
theorem outcomeProb_diagonal [Fintype d] [DecidableEq d] (E : Matrix d d ℂ) (v : d → ℝ) :
    outcomeProb E (Matrix.diagonal fun i => (v i : ℂ)) = ∑ i, (E i i).re * v i := by
  have : (E * Matrix.diagonal fun i => (v i : ℂ)).trace = ∑ i, E i i * (v i : ℂ) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.diag]
  rw [outcomeProb, this]
  simp [Complex.re_sum, Complex.mul_re]

/-! ## The Holevo bound -/

/-- The Holevo bound for an ensemble of commuting states, in the special case where the states
are already diagonal.  (The normalization hypotheses `hp1` and `hr1` are part of the data of a
quantum ensemble, but the proof only uses nonnegativity.) -/
theorem holevo_bound_diagonal [Fintype d] [DecidableEq d] [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → d → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (ρ : X → Matrix d d ℂ) (hρ : ∀ x, ρ x = Matrix.diagonal fun i => (r x i : ℂ))
    (E : Y → Matrix d d ℂ) (hE : IsPOVM E) :
    measuredInfo p ρ E ≤ holevoChi p ρ := by
  classical
  set W : Y → d → ℝ := fun y i => (E y i i).re with hW
  set rbar : d → ℝ := fun i => ∑ x, p x * r x i with hrbar
  have hW0 : ∀ y i, 0 ≤ W y i := by
    intro y i
    have h := (hE.1 y).diag_nonneg (i := i)
    rw [Complex.le_def] at h
    simpa [hW] using h.1
  have hW1 : ∀ i, ∑ y, W y i = 1 := by
    intro i
    have h : (∑ y, E y) i i = (1 : Matrix d d ℂ) i i := by rw [hE.2]
    rw [Matrix.sum_apply, Matrix.one_apply_eq] at h
    have := congrArg Complex.re h
    simpa [hW, Complex.re_sum] using this
  have hrbar0 : ∀ i, 0 ≤ rbar i := fun i =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hr0 x i)
  have hac : ∀ x, 0 < p x → ∀ i, rbar i = 0 → r x i = 0 := by
    intro x hx i hi
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => mul_nonneg (hp0 x) (hr0 x i))).1 hi x (mem_univ x)
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (ne_of_gt hx)
    · exact h'
  have hq : ∀ x y, outcomeProb (E y) (ρ x) = ∑ i, W y i * r x i := by
    intro x y; rw [hρ x, outcomeProb_diagonal]
  have hqbar : ∀ y, (∑ x, p x * outcomeProb (E y) (ρ x)) = ∑ i, W y i * rbar i := by
    intro y
    simp only [hq]
    calc ∑ x, p x * ∑ i, W y i * r x i = ∑ x, ∑ i, p x * (W y i * r x i) := by
          simp [Finset.mul_sum]
      _ = ∑ i, ∑ x, p x * (W y i * r x i) := Finset.sum_comm
      _ = ∑ i, W y i * rbar i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hrbar, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
  have hLHS : measuredInfo p ρ E
      = ∑ x, p x * ∑ y, (∑ i, W y i * r x i) *
          Real.log ((∑ i, W y i * r x i) / (∑ i, W y i * rbar i)) := by
    rw [measuredInfo]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hqbar y, hq x y, mul_assoc]
  have havg : ∑ x, p x • ρ x = Matrix.diagonal fun i => ((rbar i : ℝ) : ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.sum_apply, hρ, Matrix.diagonal_apply_eq, hrbar, Complex.ofReal_sum]
    · simp [Matrix.sum_apply, hρ, h]
  have hchi : holevoChi p ρ = ∑ x, p x * ∑ i, r x i * Real.log (r x i / rbar i) := by
    rw [holevoChi, havg, vonNeumannEntropy_diagonal]
    simp only [hρ, vonNeumannEntropy_diagonal]
    have step : ∀ x ∈ (univ : Finset X), p x * ∑ i, r x i * Real.log (r x i / rbar i)
        = p x * ((∑ i, r x i * Real.log (r x i)) - ∑ i, r x i * Real.log (rbar i)) := by
      intro x _
      rcases eq_or_lt_of_le (hp0 x) with h | h
      · rw [← h]; ring
      · congr 1
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hri : r x i = 0
        · simp [hri]
        · have hbi : rbar i ≠ 0 := fun hc => hri (hac x h i hc)
          rw [Real.log_div hri hbi]; ring
    rw [Finset.sum_congr rfl step]
    have e1 : ∀ x, ∑ i, r x i * Real.log (r x i) = - ∑ i, Real.negMulLog (r x i) := by
      intro x
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp [Real.negMulLog]
    have e2 : ∑ x, p x * ∑ i, r x i * Real.log (rbar i) = - ∑ i, Real.negMulLog (rbar i) := by
      calc ∑ x, p x * ∑ i, r x i * Real.log (rbar i)
          = ∑ x, ∑ i, p x * (r x i * Real.log (rbar i)) := by simp [Finset.mul_sum]
        _ = ∑ i, ∑ x, p x * (r x i * Real.log (rbar i)) := Finset.sum_comm
        _ = ∑ i, (∑ x, p x * r x i) * Real.log (rbar i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = - ∑ i, Real.negMulLog (rbar i) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun i _ => by simp [Real.negMulLog, hrbar]
    have e3 : ∑ x, p x * ((∑ i, r x i * Real.log (r x i)) - ∑ i, r x i * Real.log (rbar i))
        = (∑ x, p x * ∑ i, r x i * Real.log (r x i))
          - ∑ x, p x * ∑ i, r x i * Real.log (rbar i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have e4 : ∑ x, p x * ∑ i, r x i * Real.log (r x i)
        = - ∑ x, p x * ∑ i, Real.negMulLog (r x i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [e1 x]; ring
    rw [e3, e2, e4]
    ring
  rw [hLHS, hchi]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases eq_or_lt_of_le (hp0 x) with h | h
  · rw [← h]; simp
  · refine mul_le_mul_of_nonneg_left ?_ (hp0 x)
    exact kl_data_processing W hW0 hW1 (r x) rbar (hr0 x) hrbar0 (fun i hi => hac x h i hi)

/-- **Holevo bound**.  Let `(p x, ρ x)` be an ensemble of quantum states which are
simultaneously diagonalizable (equivalently, which commute with each other), i.e.
`ρ x = U * diagonal (r x) * U†` for a unitary `U` and probability vectors `r x`.  Then for
*every* POVM `E`, the classical mutual information between the label `x` and the measurement
outcome is at most the Holevo quantity `χ` of the ensemble; hence the accessible information
is at most `χ` (see `QI.accessibleInfo_le_holevoChi`).

(The normalization hypotheses `hp1` and `hr1`, which say that `p` is a probability distribution
and each `ρ x` is a density matrix, are part of the statement of the Holevo bound, but the proof
only uses nonnegativity.) -/
theorem holevo_bound [Fintype d] [DecidableEq d] [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → d → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (ρ : X → Matrix d d ℂ) (hρ : ∀ x, ρ x = U * (Matrix.diagonal fun i => (r x i : ℂ)) * star U)
    (E : Y → Matrix d d ℂ) (hE : IsPOVM E) :
    measuredInfo p ρ E ≤ holevoChi p ρ := by
  have h1 : star U * U = 1 := hU.1
  set ρ' : X → Matrix d d ℂ := fun x => Matrix.diagonal fun i => (r x i : ℂ) with hρ'
  set E' : Y → Matrix d d ℂ := fun y => star U * E y * U with hE'
  have hE'povm : IsPOVM E' := by
    refine ⟨fun y => ?_, ?_⟩
    · rw [hE', Matrix.star_eq_conjTranspose]
      exact (hE.1 y).conjTranspose_mul_mul_same U
    · calc ∑ y, E' y = star U * (∑ y, E y) * U := by
            rw [hE', Finset.mul_sum, Finset.sum_mul]
        _ = 1 := by rw [hE.2]; simp [h1]
  have hprob : ∀ x y, outcomeProb (E y) (ρ x) = outcomeProb (E' y) (ρ' x) := by
    intro x y
    rw [outcomeProb, outcomeProb, hρ x, hE']
    congr 1
    rw [show E y * (U * ρ' x * star U) = (E y * U * ρ' x) * star U by simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  have hinfo : measuredInfo p ρ E = measuredInfo p ρ' E' := by
    simp only [measuredInfo, hprob]
  have havg : ∑ x, p x • ρ x = U * (∑ x, p x • ρ' x) * star U := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by simp [hρ x, hρ']
  have hchi : holevoChi p ρ = holevoChi p ρ' := by
    rw [holevoChi, holevoChi, havg, vonNeumannEntropy_unitary_conj hU]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by
      rw [hρ x, vonNeumannEntropy_unitary_conj hU]
  rw [hinfo, hchi]
  exact holevo_bound_diagonal p hp0 hp1 r hr0 hr1 ρ' (fun x => rfl) E' hE'povm

/-- **The accessible information of a commuting ensemble is at most its Holevo `χ` quantity.**
This is the supremum form of `QI.holevo_bound`. -/
theorem accessibleInfo_le_holevoChi [Fintype d] [DecidableEq d] [Fintype X]
    {O : Type*} [Fintype O] [DecidableEq O] [Nonempty O]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → d → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (ρ : X → Matrix d d ℂ) (hρ : ∀ x, ρ x = U * (Matrix.diagonal fun i => (r x i : ℂ)) * star U) :
    accessibleInfo O p ρ ≤ holevoChi p ρ := by
  classical
  have hpovm : IsPOVM (fun o : O => if o = Classical.arbitrary O then (1 : Matrix d d ℂ) else 0) := by
    refine ⟨fun o => ?_, by simp⟩
    by_cases h : o = Classical.arbitrary O <;>
      simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]
  refine csSup_le ⟨_, ⟨_, hpovm, rfl⟩⟩ ?_
  rintro I ⟨E, hE, rfl⟩
  exact holevo_bound p hp0 hp1 r hr0 hr1 U hU ρ hρ E hE

/-! ## Tightness -/

/-- The bound is attained (and the statement is not vacuous): for the uniform ensemble of the two
orthogonal states `|0⟩⟨0|`, `|1⟩⟨1|` measured in the distinguishing basis, both the measured
information and the Holevo quantity equal `log 2`. -/
theorem measuredInfo_eq_holevoChi_of_orthogonal_pair :
    measuredInfo (fun _ : Fin 2 => (1/2 : ℝ))
        (fun x : Fin 2 => Matrix.diagonal fun i : Fin 2 => ((if x = i then (1:ℝ) else 0 : ℝ) : ℂ))
        (fun y : Fin 2 => Matrix.diagonal fun i : Fin 2 => ((if i = y then (1:ℝ) else 0 : ℝ) : ℂ))
      = Real.log 2 ∧
    holevoChi (fun _ : Fin 2 => (1/2 : ℝ))
        (fun x : Fin 2 => Matrix.diagonal fun i : Fin 2 => ((if x = i then (1:ℝ) else 0 : ℝ) : ℂ))
      = Real.log 2 := by
  constructor
  · rw [measuredInfo]
    simp only [outcomeProb_diagonal, Matrix.diagonal_apply_eq, Complex.ofReal_re]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Fin.sum_univ_two]
    ring
  · have havg : (∑ x : Fin 2, (1/2 : ℝ) •
        (Matrix.diagonal fun i : Fin 2 => ((if x = i then (1:ℝ) else 0 : ℝ) : ℂ)))
        = Matrix.diagonal (fun _ : Fin 2 => (((1/2 : ℝ)) : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
          Fin.sum_univ_two, Complex.real_smul]
        fin_cases i <;> norm_num
      · simp [Matrix.sum_apply, h]
    rw [holevoChi, havg, vonNeumannEntropy_diagonal]
    simp only [vonNeumannEntropy_diagonal]
    have h0 : ∀ x : Fin 2, ∑ i : Fin 2, Real.negMulLog (if x = i then (1:ℝ) else 0) = 0 := by
      intro x; fin_cases x <;> simp [Real.negMulLog]
    simp only [h0]
    simp [Real.negMulLog]

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

