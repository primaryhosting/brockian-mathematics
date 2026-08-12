import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (f a)

/-- Kullback–Leibler divergence of `a` from `b` (in nats), with the convention
`0 * log (0 / b) = 0` coming from `Real.log 0 = 0`. -/
noncomputable def relEntropy {α : Type*} [Fintype α] (a b : α → ℝ) : ℝ :=
  ∑ z, a z * Real.log (a z / b z)

lemma shannonEntropy_eq_neg_sum {α : Type*} [Fintype α] (f : α → ℝ) :
    shannonEntropy f = -∑ a, f a * Real.log (f a) := by
  simp only [shannonEntropy, Real.negMulLog_eq_neg, Finset.sum_neg_distrib]

/-! ### The log-sum inequality -/

/-- Pointwise ingredient of the log-sum inequality, obtained from `log x ≥ 1 - 1/x`. -/
lemma logsum_pointwise {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 < A) (hB : 0 < B) (hac : b = 0 → a = 0) :
    a - b * (A / B) ≤ a * Real.log (a / b) - a * Real.log (A / B) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · have ha0 : a = 0 := h.symm
    subst ha0
    have : 0 ≤ b * (A / B) := by positivity
    simpa using this
  · have hb' : 0 < b := by
      rcases eq_or_lt_of_le hb with h | h
      · exact absurd (hac h.symm) (ne_of_gt ha')
      · exact h
    set x : ℝ := (a * B) / (b * A) with hx
    have hxpos : 0 < x := by rw [hx]; positivity
    have hlog : 1 - 1 / x ≤ Real.log x := by
      have h1 : Real.log (1 / x) ≤ 1 / x - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (1 / x) = - Real.log x := by
        rw [one_div, Real.log_inv]
      rw [h2] at h1
      linarith
    have e1 : Real.log (a / b) = Real.log a - Real.log b := Real.log_div ha'.ne' hb'.ne'
    have e2 : Real.log (A / B) = Real.log A - Real.log B := Real.log_div hA.ne' hB.ne'
    have e3 : Real.log x = Real.log (a * B) - Real.log (b * A) := by
      rw [hx]
      exact Real.log_div (mul_ne_zero ha'.ne' hB.ne') (mul_ne_zero hb'.ne' hA.ne')
    have e4 : Real.log (a * B) = Real.log a + Real.log B := Real.log_mul ha'.ne' hB.ne'
    have e5 : Real.log (b * A) = Real.log b + Real.log A := Real.log_mul hb'.ne' hA.ne'
    have hxeq : Real.log (a / b) - Real.log (A / B) = Real.log x := by
      rw [e1, e2, e3, e4, e5]; ring
    have hstep : a * (1 - 1 / x) ≤ a * Real.log x :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt ha')
    have hinv : a * (1 / x) = b * (A / B) := by
      rw [hx, one_div, inv_div]
      field_simp
    have hgoal : a * Real.log (a / b) - a * Real.log (A / B) = a * Real.log x := by
      rw [← hxeq]; ring
    rw [hgoal]
    nlinarith [hstep, hinv]

/-- **Log-sum inequality**: `(∑ a) log ((∑ a)/(∑ b)) ≤ ∑ a log (a/b)`. -/
lemma log_sum_inequality {Z : Type*} (s : Finset Z) (a b : Z → ℝ)
    (ha : ∀ z ∈ s, 0 ≤ a z) (hb : ∀ z ∈ s, 0 ≤ b z)
    (hac : ∀ z ∈ s, b z = 0 → a z = 0) :
    (∑ z ∈ s, a z) * Real.log ((∑ z ∈ s, a z) / (∑ z ∈ s, b z))
      ≤ ∑ z ∈ s, a z * Real.log (a z / b z) := by
  have hA0 : 0 ≤ ∑ z ∈ s, a z := Finset.sum_nonneg ha
  rcases eq_or_lt_of_le hA0 with h | hApos
  · have hzero : ∀ z ∈ s, a z = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 h.symm
    have hR : ∑ z ∈ s, a z * Real.log (a z / b z) = 0 :=
      Finset.sum_eq_zero fun z hz => by rw [hzero z hz]; ring
    rw [hR, ← h, zero_mul]
  · have hex : ∃ z ∈ s, 0 < a z := by
      by_contra hcon
      push_neg at hcon
      have : ∑ z ∈ s, a z = 0 :=
        Finset.sum_eq_zero fun z hz => le_antisymm (hcon z hz) (ha z hz)
      exact absurd this (ne_of_gt hApos)
    obtain ⟨z0, hz0s, hz0⟩ := hex
    have hbz0 : 0 < b z0 := by
      rcases eq_or_lt_of_le (hb z0 hz0s) with h | h
      · exact absurd (hac z0 hz0s h.symm) (ne_of_gt hz0)
      · exact h
    have hBpos : 0 < ∑ z ∈ s, b z := Finset.sum_pos' hb ⟨z0, hz0s, hbz0⟩
    have key : ∀ z ∈ s, a z - b z * ((∑ w ∈ s, a w) / (∑ w ∈ s, b w))
        ≤ a z * Real.log (a z / b z)
          - a z * Real.log ((∑ w ∈ s, a w) / (∑ w ∈ s, b w)) :=
      fun z hz => logsum_pointwise (ha z hz) (hb z hz) hApos hBpos (hac z hz)
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul] at hsum
    have hBA : (∑ z ∈ s, b z) * ((∑ w ∈ s, a w) / (∑ w ∈ s, b w)) = ∑ w ∈ s, a w := by
      field_simp
    rw [hBA] at hsum
    linarith

/-! ### Monotonicity of relative entropy under a classical channel -/

/-- Relative entropy does not increase under a stochastic map (classical data processing). -/
lemma relEntropy_channel_le {Z Y : Type*} [Fintype Z] [Fintype Y]
    (a b : Z → ℝ) (E : Y → Z → ℝ)
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hac : ∀ z, b z = 0 → a z = 0)
    (hE0 : ∀ y z, 0 ≤ E y z) (hE1 : ∀ z, ∑ y, E y z = 1) :
    ∑ y, (∑ z, a z * E y z) * Real.log ((∑ z, a z * E y z) / (∑ z, b z * E y z))
      ≤ ∑ z, a z * Real.log (a z / b z) := by
  have step : ∀ y : Y,
      (∑ z, a z * E y z) * Real.log ((∑ z, a z * E y z) / (∑ z, b z * E y z))
        ≤ ∑ z, E y z * (a z * Real.log (a z / b z)) := by
    intro y
    have h := log_sum_inequality (Finset.univ : Finset Z)
      (fun z => a z * E y z) (fun z => b z * E y z)
      (fun z _ => mul_nonneg (ha z) (hE0 y z))
      (fun z _ => mul_nonneg (hb z) (hE0 y z))
      (by
        intro z _ hz
        simp only at hz ⊢
        rcases mul_eq_zero.1 hz with h1 | h1
        · simp [hac z h1]
        · simp [h1])
    refine h.trans_eq ?_
    refine Finset.sum_congr rfl ?_
    intro z _
    show a z * E y z * Real.log (a z * E y z / (b z * E y z))
      = E y z * (a z * Real.log (a z / b z))
    rcases eq_or_lt_of_le (hE0 y z) with hE | hE
    · rw [← hE]; simp
    · rw [mul_div_mul_right _ _ hE.ne']; ring
  calc ∑ y, (∑ z, a z * E y z) * Real.log ((∑ z, a z * E y z) / (∑ z, b z * E y z))
      ≤ ∑ y, ∑ z, E y z * (a z * Real.log (a z / b z)) :=
        Finset.sum_le_sum (fun y _ => step y)
    _ = ∑ z, a z * Real.log (a z / b z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [← Finset.sum_mul, hE1 z, one_mul]

/-! ### The classical Holevo quantity -/

/-- The Holevo quantity of a classical ensemble equals the average relative entropy to the
average distribution. -/
lemma chi_eq_sum_relEntropy {ι Z : Type*} [Fintype ι] [Fintype Z]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (r : ι → Z → ℝ) (hr0 : ∀ i z, 0 ≤ r i z)
    (rbar : Z → ℝ) (hrb : ∀ z, rbar z = ∑ j, p j * r j z) :
    ∑ i, p i * relEntropy (r i) rbar
      = shannonEntropy rbar - ∑ i, p i * shannonEntropy (r i) := by
  have hsplit : ∀ i, p i * relEntropy (r i) rbar
      = p i * (∑ z, r i z * Real.log (r i z)) - p i * (∑ z, r i z * Real.log (rbar z)) := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · rw [← hpi]; ring
    · have hre : relEntropy (r i) rbar
          = (∑ z, r i z * Real.log (r i z)) - (∑ z, r i z * Real.log (rbar z)) := by
        rw [relEntropy, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro z _
        rcases eq_or_lt_of_le (hr0 i z) with hz | hz
        · rw [← hz]; ring
        · have hrb' : 0 < rbar z := by
            rw [hrb z]
            refine lt_of_lt_of_le (mul_pos hpi hz) ?_
            exact Finset.single_le_sum (f := fun j => p j * r j z)
              (fun j _ => mul_nonneg (hp0 j) (hr0 j z)) (Finset.mem_univ i)
          rw [Real.log_div (ne_of_gt hz) (ne_of_gt hrb')]
          ring
      rw [hre]; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsplit i), Finset.sum_sub_distrib]
  have h1 : ∑ i, p i * (∑ z, r i z * Real.log (r i z)) = -∑ i, p i * shannonEntropy (r i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [shannonEntropy_eq_neg_sum]
    ring
  have h2 : ∑ i, p i * (∑ z, r i z * Real.log (rbar z)) = -shannonEntropy rbar := by
    have hcomm : ∑ i, p i * (∑ z, r i z * Real.log (rbar z))
        = ∑ z, rbar z * Real.log (rbar z) := by
      simp only [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro z _
      rw [← Finset.sum_mul, ← hrb z]
    rw [hcomm, shannonEntropy_eq_neg_sum, neg_neg]
  rw [h1, h2]
  ring

/-- **Classical Holevo bound**: for an ensemble of probability vectors `r i` with prior `p`,
and any classical channel `E`, the mutual information between the label and the outcome is at
most the Holevo quantity `H(∑ p i r i) - ∑ p i H(r i)`. -/
theorem holevo_bound_classical {ι Z Y : Type*} [Fintype ι] [Fintype Z] [Fintype Y]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (r : ι → Z → ℝ) (hr0 : ∀ i z, 0 ≤ r i z)
    (E : Y → Z → ℝ) (hE0 : ∀ y z, 0 ≤ E y z) (hE1 : ∀ z, ∑ y, E y z = 1)
    (rbar : Z → ℝ) (hrb : ∀ z, rbar z = ∑ j, p j * r j z) :
    ∑ i, ∑ y, p i * ((∑ z, r i z * E y z) *
        Real.log ((∑ z, r i z * E y z) / (∑ j, p j * (∑ z, r j z * E y z))))
      ≤ shannonEntropy rbar - ∑ i, p i * shannonEntropy (r i) := by
  have hrbar0 : ∀ z, 0 ≤ rbar z := by
    intro z
    rw [hrb z]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (hr0 j z)
  have hwbar : ∀ y : Y, (∑ j, p j * (∑ z, r j z * E y z)) = ∑ z, rbar z * E y z := by
    intro y
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro z _
    rw [← Finset.sum_mul, ← hrb z]
  have main : ∀ i : ι, p i * (∑ y, (∑ z, r i z * E y z) *
      Real.log ((∑ z, r i z * E y z) / (∑ z, rbar z * E y z)))
      ≤ p i * relEntropy (r i) rbar := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · rw [← hpi]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpi)
      exact relEntropy_channel_le (r i) rbar E (hr0 i) hrbar0
        (by
          intro z hz
          by_contra hne
          have hz' : 0 < r i z := lt_of_le_of_ne (hr0 i z) (Ne.symm hne)
          have hpos : 0 < rbar z := by
            rw [hrb z]
            refine lt_of_lt_of_le (mul_pos hpi hz') ?_
            exact Finset.single_le_sum (f := fun j => p j * r j z)
              (fun j _ => mul_nonneg (hp0 j) (hr0 j z)) (Finset.mem_univ i)
          exact absurd hz (ne_of_gt hpos))
        hE0 hE1
  calc ∑ i, ∑ y, p i * ((∑ z, r i z * E y z) *
        Real.log ((∑ z, r i z * E y z) / (∑ j, p j * (∑ z, r j z * E y z))))
      = ∑ i, p i * (∑ y, (∑ z, r i z * E y z) *
          Real.log ((∑ z, r i z * E y z) / (∑ z, rbar z * E y z))) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [hwbar y]
    _ ≤ ∑ i, p i * relEntropy (r i) rbar := Finset.sum_le_sum (fun i _ => main i)
    _ = shannonEntropy rbar - ∑ i, p i * shannonEntropy (r i) :=
        chi_eq_sum_relEntropy p hp0 r hr0 rbar hrb

/-! ### The quantum setting -/

section Quantum

open Matrix Polynomial
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The density matrix of a state which is diagonal in a fixed orthonormal basis, with
spectrum `r`. -/
noncomputable def diagState (r : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal (fun z => (r z : ℂ))

omit [Fintype n] in
lemma diagState_isHermitian (r : n → ℝ) : (diagState r).IsHermitian := by
  rw [diagState, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  ext i j
  simp [Matrix.diagonal]

/-- Von Neumann entropy `S(ρ) = -tr (ρ log ρ)` of a density matrix, in nats, defined as the
Shannon entropy of its spectrum. -/
noncomputable def vonNeumannEntropy (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

/-- The eigenvalues of a real diagonal matrix are its diagonal entries, up to a permutation;
hence any symmetric function of the spectrum can be computed on the diagonal. -/
lemma sum_eigenvalues_diagState (r : n → ℝ) (g : ℝ → ℝ)
    (hA : (diagState r).IsHermitian) :
    ∑ i, g (hA.eigenvalues i) = ∑ z, g (r z) := by
  have h1 : (diagState r).charpoly.roots
      = Multiset.map (fun z => ((r z : ℝ) : ℂ)) (Finset.univ : Finset n).val := by
    rw [diagState, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hA.roots_charpoly_eq_eigenvalues
  rw [h1] at h2
  have h3 : Multiset.map hA.eigenvalues (Finset.univ : Finset n).val
      = Multiset.map (fun z => (r z : ℝ)) (Finset.univ : Finset n).val := by
    have := congrArg (Multiset.map Complex.re) h2
    simpa [Multiset.map_map, Function.comp_def] using this.symm
  have h4 := congrArg (Multiset.map g) h3
  simp only [Multiset.map_map, Function.comp_def] at h4
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact congrArg Multiset.sum h4

lemma vonNeumannEntropy_diagState (r : n → ℝ) :
    vonNeumannEntropy (diagState r) = shannonEntropy r := by
  rw [vonNeumannEntropy, dif_pos (diagState_isHermitian r), shannonEntropy]
  exact sum_eigenvalues_diagState r Real.negMulLog (diagState_isHermitian r)

/-- Born rule: the probability of outcome `E` on the state `ρ`. -/
noncomputable def bornProb (E : Matrix n n ℂ) (rho : Matrix n n ℂ) : ℝ :=
  ((E * rho).trace).re

lemma bornProb_diagState (E : Matrix n n ℂ) (r : n → ℝ) :
    bornProb E (diagState r) = ∑ z, r z * (E z z).re := by
  rw [bornProb, diagState]
  have : (E * Matrix.diagonal (fun z => (r z : ℂ))).trace = ∑ z, E z z * (r z : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal]
  rw [this, Complex.re_sum]
  exact Finset.sum_congr rfl (fun z _ => by simp [Complex.mul_re]; ring)

/-- Mutual information (in nats) between the label `i` (with prior `p`) and the measurement
outcome `y`, where `q i y` is the conditional probability of outcome `y` given label `i`.
Maximising this over measurements gives the accessible information. -/
noncomputable def accessibleInfoOf {ι Y : Type*} [Fintype ι] [Fintype Y]
    (p : ι → ℝ) (q : ι → Y → ℝ) : ℝ :=
  ∑ i, ∑ y, p i * (q i y * Real.log (q i y / ∑ j, p j * q j y))

/-- The Holevo `χ` quantity of the ensemble `{p i, ρ i}`. -/
noncomputable def holevoChi {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (rho : ι → Matrix n n ℂ) : ℝ :=
  vonNeumannEntropy (∑ i, (p i : ℂ) • rho i) - ∑ i, p i * vonNeumannEntropy (rho i)

omit [Fintype n] in
lemma sum_smul_diagState {ι : Type*} [Fintype ι] (p : ι → ℝ) (r : ι → n → ℝ) :
    (∑ i, (p i : ℂ) • diagState (r i)) = diagState (fun z => ∑ j, p j * r j z) := by
  ext z w
  by_cases h : z = w
  · subst h
    simp [diagState, Matrix.sum_apply, Matrix.diagonal]
  · simp [diagState, Matrix.sum_apply, Matrix.diagonal, h]

/-! ### Commuting ensembles -/

/-- A density matrix which is diagonal in the orthonormal basis given by the columns of the
unitary `U`, with spectrum `r`. An ensemble of such states sharing one `U` is exactly an
ensemble of pairwise commuting density matrices. -/
noncomputable def commutingState (U : Matrix n n ℂ) (r : n → ℝ) : Matrix n n ℂ :=
  U * diagState r * Uᴴ

omit [DecidableEq n] in
lemma isHermitian_conj (U A : Matrix n n ℂ) (hA : A.IsHermitian) : (U * A * Uᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

lemma charpoly_conj_unitary (U A : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    (U * A * Uᴴ).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma commutingState_isHermitian (U : Matrix n n ℂ) (r : n → ℝ) :
    (commutingState U r).IsHermitian :=
  isHermitian_conj U _ (diagState_isHermitian r)

lemma vonNeumannEntropy_commutingState (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (r : n → ℝ) :
    vonNeumannEntropy (commutingState U r) = shannonEntropy r := by
  have hH : (commutingState U r).IsHermitian := commutingState_isHermitian U r
  have hD : (diagState r).IsHermitian := diagState_isHermitian r
  have hev : hH.eigenvalues = hD.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hA := hH) (hB := hD)).2
      (charpoly_conj_unitary U (diagState r) hU)
  rw [vonNeumannEntropy, dif_pos hH, hev, shannonEntropy]
  exact sum_eigenvalues_diagState r Real.negMulLog hD

lemma sum_smul_commutingState {ι : Type*} [Fintype ι] (U : Matrix n n ℂ)
    (p : ι → ℝ) (r : ι → n → ℝ) :
    (∑ i, (p i : ℂ) • commutingState U (r i))
      = commutingState U (fun z => ∑ j, p j * r j z) := by
  simp only [commutingState]
  rw [← sum_smul_diagState p r, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by simp)

lemma bornProb_commutingState (E U : Matrix n n ℂ) (r : n → ℝ) :
    bornProb E (commutingState U r) = bornProb (Uᴴ * E * U) (diagState r) := by
  rw [bornProb, bornProb, commutingState, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **Holevo bound.** Let `{p i, ρ i}` be an ensemble of pairwise commuting density matrices,
i.e. states `ρ i = U * diag (r i) * Uᴴ` diagonal in one common orthonormal basis (the columns of
the unitary `U`), with spectra `r i`. For an arbitrary POVM `{E y}`, the mutual information
between the label `i` and the measurement outcome `y` — and hence the accessible information,
which is its maximum over all measurements — is at most the Holevo quantity
`χ = S(∑ p i ρ i) - ∑ p i S(ρ i)`.

The normalisation hypotheses `hp1` and `hr1` (which say that `p` is a probability vector and
each `ρ i` has unit trace) are part of the definition of a quantum ensemble; they are recorded
here for faithfulness even though the inequality itself does not need them. -/
theorem holevo_bound {ι Y : Type*} [Fintype ι] [Fintype Y]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (r : ι → n → ℝ) (hr0 : ∀ i z, 0 ≤ r i z) (hr1 : ∀ i, ∑ z, r i z = 1)
    (E : Y → Matrix n n ℂ) (hE : ∀ y, (E y).PosSemidef) (hEsum : ∑ y, E y = 1) :
    accessibleInfoOf p (fun i y => bornProb (E y) (commutingState U (r i)))
      ≤ holevoChi p (fun i => commutingState U (r i)) := by
  classical
  set F : Y → Matrix n n ℂ := fun y => Uᴴ * E y * U with hF
  have hFpsd : ∀ y, (F y).PosSemidef := fun y => (hE y).conjTranspose_mul_mul_same U
  have hFsum : ∑ y, F y = 1 := by
    simp only [hF]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hEsum, Matrix.mul_one, hU]
  set c : Y → n → ℝ := fun y z => ((F y) z z).re with hc
  have hc0 : ∀ y z, 0 ≤ c y z := by
    intro y z
    have h := (hFpsd y).diag_nonneg (i := z)
    rw [Complex.le_def] at h
    simpa [hc] using h.1
  have hc1 : ∀ z, ∑ y, c y z = 1 := by
    intro z
    have h : ∑ y, (F y) z z = (1 : Matrix n n ℂ) z z := by
      rw [← hFsum, Matrix.sum_apply]
    have h2 : ∑ y, c y z = (∑ y, (F y) z z).re := by
      rw [Complex.re_sum]
    rw [h2, h]
    simp
  have hborn : ∀ i y, bornProb (E y) (commutingState U (r i)) = ∑ z, r i z * c y z := by
    intro i y
    rw [bornProb_commutingState, bornProb_diagState]
  have hchi : holevoChi p (fun i => commutingState U (r i))
      = shannonEntropy (fun z => ∑ j, p j * r j z) - ∑ i, p i * shannonEntropy (r i) := by
    rw [holevoChi, sum_smul_commutingState, vonNeumannEntropy_commutingState U hU]
    refine congrArg₂ _ rfl ?_
    exact Finset.sum_congr rfl (fun i _ => by rw [vonNeumannEntropy_commutingState U hU])
  rw [hchi, accessibleInfoOf]
  simp only [hborn]
  exact holevo_bound_classical p hp0 r hr0 c hc0 hc1 _ (fun z => rfl)

/-- Non-vacuity check: the hypotheses of `holevo_bound` are satisfiable by a genuinely
informative measurement — for any ensemble of states diagonal in the computational basis, the
projective measurement in that basis is a POVM to which the bound applies. -/
example {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (r : ι → n → ℝ) (hr0 : ∀ i z, 0 ≤ r i z) (hr1 : ∀ i, ∑ z, r i z = 1) :
    accessibleInfoOf p (fun i y =>
        bornProb (Matrix.diagonal (fun w => if w = y then (1 : ℂ) else 0))
          (commutingState 1 (r i)))
      ≤ holevoChi p (fun i => commutingState 1 (r i)) := by
  refine holevo_bound p hp0 hp1 1 (by simp) r hr0 hr1 _ ?_ ?_
  · intro y
    rw [Matrix.posSemidef_diagonal_iff]
    intro w
    by_cases h : w = y <;> simp [h]
  · ext a b
    by_cases h : a = b
    · subst h; simp [Matrix.sum_apply, Matrix.diagonal]
    · simp [Matrix.sum_apply, Matrix.diagonal, h]

end Quantum

end QI

