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
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/
noncomputable def shannonEntropy [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- Mutual information of a joint distribution `r` on `X × Y`. -/
noncomputable def mutualInfo [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))

/-- The log-sum inequality. -/
lemma log_sum_le [Fintype I] (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hac : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hAdef
  set B := ∑ i, b i with hBdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have h2 : ∑ i, a i = 0 := by rw [← hAdef]; exact hA0.symm
    have hall : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 h2 i (Finset.mem_univ i)
    simp [hall, ← hA0]
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · exfalso
    have h2 : ∑ i, b i = 0 := by rw [← hBdef]; exact hB0.symm
    have hall : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 h2 i (Finset.mem_univ i)
    have : A = 0 := by
      rw [hAdef]; exact Finset.sum_eq_zero fun i _ => hac i (hall i)
    exact absurd this (ne_of_gt hApos)
  · set c := A / B with hc
    have hcpos : 0 < c := div_pos hApos hBpos
    have hcB : c * B = A := div_mul_cancel₀ A (ne_of_gt hBpos)
    have key : ∀ i ∈ (univ : Finset I),
        a i * Real.log c + (a i - c * b i) ≤ a i * Real.log (a i / b i) := by
      intro i _
      rcases eq_or_lt_of_le (ha i) with h0 | hpos
      · simp [← h0]
        exact mul_nonneg hcpos.le (hb i)
      · have hbi : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with h | h
          · exact absurd (hac i h.symm) (ne_of_gt hpos)
          · exact h
        set t := a i / (b i * c) with ht
        have htpos : 0 < t := div_pos hpos (mul_pos hbi hcpos)
        have hlog : 1 - 1 / t ≤ Real.log t := by
          have h := Real.log_le_sub_one_of_pos (x := 1 / t) (by positivity)
          rw [Real.log_div one_ne_zero (ne_of_gt htpos), Real.log_one] at h
          rw [one_div] at h ⊢
          linarith
        have hlt : Real.log t = Real.log (a i) - Real.log (b i) - Real.log c := by
          rw [ht, Real.log_div (ne_of_gt hpos) (by positivity),
            Real.log_mul (ne_of_gt hbi) (ne_of_gt hcpos)]
          ring
        have hsplit : Real.log (a i / b i) = Real.log t + Real.log c := by
          rw [hlt, Real.log_div (ne_of_gt hpos) (ne_of_gt hbi)]; ring
        rw [hsplit]
        have h1t : a i * (1 / t) = c * b i := by rw [ht]; field_simp
        have hkey : a i - c * b i ≤ a i * Real.log t := by
          have h := mul_le_mul_of_nonneg_left hlog hpos.le
          rw [mul_sub, mul_one, h1t] at h
          linarith
        nlinarith [hkey]
    calc A * Real.log c = ∑ i, (a i * Real.log c + (a i - c * b i)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
            ← hAdef, ← hBdef, hcB]
          ring
      _ ≤ ∑ i, a i * Real.log (a i / b i) := Finset.sum_le_sum key

/-- Data-processing for the relative entropy of two nonnegative vectors under a stochastic
kernel `M`. -/
lemma sum_log_channel_le [Fintype I] [Fintype Y] (u v : I → ℝ) (M : I → Y → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (hM0 : ∀ i y, 0 ≤ M i y)
    (hM1 : ∀ i, ∑ y, M i y = 1) (hac : ∀ i, v i = 0 → u i = 0) :
    ∑ y, (∑ i, u i * M i y) * Real.log ((∑ i, u i * M i y) / (∑ i, v i * M i y))
      ≤ ∑ i, u i * Real.log (u i / v i) := by
  have key : ∀ y ∈ (univ : Finset Y),
      (∑ i, u i * M i y) * Real.log ((∑ i, u i * M i y) / (∑ i, v i * M i y))
        ≤ ∑ i, (u i * Real.log (u i / v i)) * M i y := by
    intro y _
    refine le_trans (log_sum_le (fun i => u i * M i y) (fun i => v i * M i y)
      (fun i => mul_nonneg (hu i) (hM0 i y)) (fun i => mul_nonneg (hv i) (hM0 i y)) ?_) ?_
    · intro i h
      simp only at h ⊢
      rcases mul_eq_zero.1 h with h1 | h1
      · rw [hac i h1]; ring
      · rw [h1]; ring
    · refine Finset.sum_le_sum fun i _ => le_of_eq ?_
      simp only
      rcases eq_or_lt_of_le (hM0 i y) with h0 | hpos
      · rw [← h0]; ring
      rcases eq_or_lt_of_le (hv i) with h0 | hvpos
      · rw [hac i h0.symm]; ring
      · rw [mul_div_mul_right _ _ (ne_of_gt hpos)]; ring
  refine le_trans (Finset.sum_le_sum key) (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, hM1 i, mul_one]

/-- Data-processing inequality for the mutual information: post-processing the second
component of a joint distribution through a stochastic kernel cannot increase the mutual
information. -/
lemma mutualInfo_channel_le [Fintype X] [Fintype I] [Fintype Y] (r : X → I → ℝ)
    (hr : ∀ x i, 0 ≤ r x i) (M : I → Y → ℝ) (hM0 : ∀ i y, 0 ≤ M i y)
    (hM1 : ∀ i, ∑ y, M i y = 1) :
    mutualInfo (fun x y => ∑ i, r x i * M i y) ≤ mutualInfo r := by
  have hrow : ∀ x, ∑ y, (∑ i, r x i * M i y) = ∑ i, r x i := by
    intro x
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, hM1 i, mul_one]
  have hcol : ∀ y, ∑ x, (∑ i, r x i * M i y) = ∑ i, (∑ x', r x' i) * M i y := by
    intro y
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  unfold mutualInfo
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [hrow, hcol]
  have hv : ∀ y, (∑ i, r x i) * (∑ i, (∑ x', r x' i) * M i y)
      = ∑ i, ((∑ i', r x i') * (∑ x', r x' i)) * M i y := by
    intro y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hv]
  exact sum_log_channel_le (r x) (fun i => (∑ i', r x i') * (∑ x', r x' i)) M
    (fun i => hr x i)
    (fun i => mul_nonneg (Finset.sum_nonneg fun _ _ => hr x _) (Finset.sum_nonneg fun _ _ => hr _ i))
    hM0 hM1 (by
      intro i h
      rcases mul_eq_zero.1 h with h1 | h1
      · exact le_antisymm (h1 ▸ Finset.single_le_sum (f := fun i' => r x i')
          (fun i' _ => hr x i') (Finset.mem_univ i)) (hr x i)
      · exact le_antisymm (h1 ▸ Finset.single_le_sum (f := fun x' => r x' i)
          (fun x' _ => hr x' i) (Finset.mem_univ x)) (hr x i))

/-- For a joint distribution of the form `r x i = p x * q x i` with each `q x` a probability
vector, the mutual information is the entropy of the average minus the average entropy. -/
lemma mutualInfo_mk [Fintype X] [Fintype I] (p : X → ℝ) (q : X → I → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq0 : ∀ x i, 0 ≤ q x i) (hq1 : ∀ x, ∑ i, q x i = 1) :
    mutualInfo (fun x i => p x * q x i)
      = shannonEntropy (fun i => ∑ x, p x * q x i) - ∑ x, p x * shannonEntropy (q x) := by
  have hmarg1 : ∀ x, ∑ i', p x * q x i' = p x := fun x => by rw [← Finset.mul_sum, hq1 x, mul_one]
  have term : ∀ x i, (p x * q x i) * Real.log ((p x * q x i) / (p x * ∑ x', p x' * q x' i))
      = p x * (q x i * Real.log (q x i))
        - (p x * q x i) * Real.log (∑ x', p x' * q x' i) := by
    intro x i
    rcases eq_or_lt_of_le (hp x) with h0 | hppos
    · rw [← h0]; ring
    rcases eq_or_lt_of_le (hq0 x i) with h0 | hqpos
    · rw [← h0]; simp
    have hqb0 : 0 < ∑ x', p x' * q x' i := lt_of_lt_of_le (mul_pos hppos hqpos)
      (Finset.single_le_sum (f := fun x' => p x' * q x' i)
        (fun x' _ => mul_nonneg (hp x') (hq0 x' i)) (Finset.mem_univ x))
    rw [mul_div_mul_left _ _ (ne_of_gt hppos), Real.log_div (ne_of_gt hqpos) (ne_of_gt hqb0)]
    ring
  unfold mutualInfo shannonEntropy
  simp only [hmarg1, term]
  have hA : ∀ x, ∑ i, (p x * (q x i * Real.log (q x i))
        - (p x * q x i) * Real.log (∑ x', p x' * q x' i))
      = p x * (∑ i, q x i * Real.log (q x i))
        - ∑ i, (p x * q x i) * Real.log (∑ x', p x' * q x' i) := by
    intro x; rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [hA]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have h1 : ∀ x, p x * (∑ i, q x i * Real.log (q x i)) = - (p x * ∑ i, Real.negMulLog (q x i)) := by
    intro x
    simp [Real.negMulLog, Finset.mul_sum]
  have h2 : ∑ i, ∑ x, (p x * q x i) * Real.log (∑ x', p x' * q x' i)
      = - ∑ i, Real.negMulLog (∑ x, p x * q x i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    simp [Real.negMulLog]
  rw [h2]
  simp only [h1]
  rw [Finset.sum_neg_distrib]
  ring

/-! ## Quantum states, measurements and entropies -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensity (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- A POVM indexed by the outcome set `Y`. -/
def IsPOVM [Fintype Y] (E : Y → Matrix n n ℂ) : Prop :=
  (∀ y, (E y).PosSemidef) ∧ ∑ y, E y = 1

open Classical in
/-- The von Neumann entropy of a Hermitian matrix (defined as `0` on non-Hermitian input). -/
noncomputable def vonNeumannEntropy (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

/-- The Holevo χ quantity of the ensemble `{p x, ρ x}`. -/
noncomputable def holevoChi [Fintype X] (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x) - ∑ x, p x * vonNeumannEntropy (ρ x)

/-- The joint distribution of the label `x` and the measurement outcome `y` obtained by
measuring the ensemble `{p x, ρ x}` with the POVM `E`. -/
noncomputable def measJoint [Fintype X] [Fintype Y] (p : X → ℝ) (ρ : X → Matrix n n ℂ)
    (E : Y → Matrix n n ℂ) : X → Y → ℝ :=
  fun x y => p x * (Matrix.trace (ρ x * E y)).re

/-- The accessible information of the ensemble `{p x, ρ x}` with respect to measurements with
outcomes in `Y`: the supremum of the mutual information over all POVMs. -/
noncomputable def accessibleInfo [Fintype X] (p : X → ℝ) (ρ : X → Matrix n n ℂ)
    (Y : Type) [Fintype Y] : ℝ :=
  sSup {t | ∃ E : Y → Matrix n n ℂ, IsPOVM E ∧ t = mutualInfo (measJoint p ρ E)}

/-- A family of matrices that is simultaneously diagonalizable by a unitary; for Hermitian
matrices this is equivalent to the family being commuting. -/
def SimultaneouslyDiagonalizable [Fintype X] (ρ : X → Matrix n n ℂ) : Prop :=
  ∃ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ ∧
    ∀ x, ∃ d : n → ℝ, ρ x = U * diagonal (fun i => (d i : ℂ)) * star U

/-- If the characteristic polynomial of a Hermitian matrix splits with real roots `d`, its
von Neumann entropy is the Shannon entropy of `d`. -/
lemma vonNeumannEntropy_eq_of_charpoly {A : Matrix n n ℂ} (hA : A.IsHermitian) (d : n → ℝ)
    (h : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((d i : ℂ)))) :
    vonNeumannEntropy A = shannonEntropy d := by
  have hroots : A.charpoly.roots = Multiset.map (fun i => ((d i : ℂ))) Finset.univ.val := by
    rw [h, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 : Multiset.map (fun i => ((hA.eigenvalues i : ℂ))) Finset.univ.val
      = Multiset.map (fun i => ((d i : ℂ))) Finset.univ.val := by
    rw [← hroots, hA.roots_charpoly_eq_eigenvalues]
    rfl
  have h3 : Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    rw [show (fun i => ((hA.eigenvalues i : ℂ))) = (fun r : ℝ => (r : ℂ)) ∘ hA.eigenvalues from rfl,
      show (fun i => ((d i : ℂ))) = (fun r : ℝ => (r : ℂ)) ∘ d from rfl,
      ← Multiset.map_map, ← Multiset.map_map] at h2
    exact Multiset.map_injective Complex.ofReal_injective h2
  have h4 : ∑ i, Real.negMulLog (hA.eigenvalues i) = ∑ i, Real.negMulLog (d i) := by
    have h5 := congrArg (fun m => (Multiset.map Real.negMulLog m).sum) h3
    simp only [Multiset.map_map] at h5
    rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
    exact h5
  rw [vonNeumannEntropy, dif_pos hA, shannonEntropy, h4]

omit [Fintype n] in
/-- A diagonal matrix with real entries is Hermitian. -/
lemma isHermitian_diagonal_real (d : n → ℝ) : (diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; simp

/-- The von Neumann entropy of a diagonal state is the Shannon entropy of its diagonal. -/
lemma vonNeumannEntropy_diagonal (d : n → ℝ) :
    vonNeumannEntropy (diagonal (fun i => (d i : ℂ))) = shannonEntropy d :=
  vonNeumannEntropy_eq_of_charpoly (isHermitian_diagonal_real d) d (Matrix.charpoly_diagonal _)

/-! ## The Holevo bound -/

/-- Holevo's bound for an ensemble of states that are diagonal in the computational basis,
measured by an arbitrary POVM. -/
theorem holevo_bound_diagonal {X : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (q : X → n → ℝ) (hq0 : ∀ x i, 0 ≤ q x i) (hq1 : ∀ x, ∑ i, q x i = 1)
    (E : Y → Matrix n n ℂ) (hE : IsPOVM E) :
    mutualInfo (measJoint p (fun x => diagonal fun i => (q x i : ℂ)) E)
      ≤ holevoChi p (fun x => diagonal fun i => (q x i : ℂ)) := by
  set M : n → Y → ℝ := fun i y => (E y i i).re with hMdef
  have hM0 : ∀ i y, 0 ≤ M i y := fun i y => (Complex.le_def.1 ((hE.1 y).diag_nonneg (i := i))).1
  have hM1 : ∀ i, ∑ y, M i y = 1 := by
    intro i
    have h : ∑ y, E y i i = (1 : ℂ) := by
      have := congrFun (congrFun hE.2 i) i
      simpa [Matrix.sum_apply] using this
    have h2 := congrArg Complex.re h
    rw [Complex.re_sum] at h2
    simpa [hMdef] using h2
  have hjoint : measJoint p (fun x => diagonal fun i => (q x i : ℂ)) E
      = fun x y => ∑ i, (p x * q x i) * M i y := by
    funext x y
    rw [measJoint]
    have htr : Matrix.trace ((diagonal fun i => (q x i : ℂ)) * E y)
        = ∑ i, (q x i : ℂ) * E y i i := by
      simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    rw [htr, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [hMdef]; ring
  have hchi : holevoChi p (fun x => diagonal fun i => (q x i : ℂ))
      = shannonEntropy (fun i => ∑ x, p x * q x i) - ∑ x, p x * shannonEntropy (q x) := by
    rw [holevoChi]
    have havg : ∑ x, (p x : ℂ) • (diagonal fun i => (q x i : ℂ))
        = diagonal (fun i => ((∑ x, p x * q x i : ℝ) : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.sum_apply]
    rw [havg, vonNeumannEntropy_diagonal]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by rw [vonNeumannEntropy_diagonal]
  rw [hjoint, hchi]
  calc mutualInfo (fun x y => ∑ i, (p x * q x i) * M i y)
      ≤ mutualInfo (fun x i => p x * q x i) :=
        mutualInfo_channel_le _ (fun x i => mul_nonneg (hp0 x) (hq0 x i)) M hM0 hM1
    _ = _ := mutualInfo_mk p q hp0 hq0 hq1

/-- The characteristic polynomial is invariant under unitary conjugation. -/
lemma charpoly_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) : (U * A * star U).charpoly = A.charpoly := by
  rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, Matrix.mem_unitaryGroup_iff'.1 hU, mul_one]

/-- A unitary conjugate of a real diagonal matrix is Hermitian. -/
lemma isHermitian_unitary_conj_diagonal (U : Matrix n n ℂ) (d : n → ℝ) :
    (U * diagonal (fun i => (d i : ℂ)) * star U).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (isHermitian_diagonal_real d).eq, ← Matrix.star_eq_conjTranspose, mul_assoc]

/-- The von Neumann entropy of a unitary conjugate of a real diagonal matrix is the Shannon
entropy of the diagonal. -/
lemma vonNeumannEntropy_unitary_conj_diagonal {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (d : n → ℝ) :
    vonNeumannEntropy (U * diagonal (fun i => (d i : ℂ)) * star U) = shannonEntropy d :=
  vonNeumannEntropy_eq_of_charpoly (isHermitian_unitary_conj_diagonal U d) d
    (by rw [charpoly_unitary_conj hU, Matrix.charpoly_diagonal])

/-- Holevo's bound for a fixed POVM `E`: the mutual information between the label and the
measurement outcome is at most the Holevo χ quantity of the ensemble. -/
theorem holevo_bound_of_POVM {X : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hcomm : SimultaneouslyDiagonalizable ρ)
    (E : Y → Matrix n n ℂ) (hE : IsPOVM E) :
    mutualInfo (measJoint p ρ E) ≤ holevoChi p ρ := by
  obtain ⟨U, hU, hdiag⟩ := hcomm
  choose q hq using hdiag
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hDpsd : ∀ x, (diagonal (fun i => (q x i : ℂ))).PosSemidef := by
    intro x
    have h := ((hρ x).1).conjTranspose_mul_mul_same U
    rw [← Matrix.star_eq_conjTranspose, hq x] at h
    have hEq : star U * (U * diagonal (fun i => (q x i : ℂ)) * star U) * U
        = diagonal (fun i => (q x i : ℂ)) := by
      simp only [mul_assoc]
      rw [hUU, mul_one, ← mul_assoc, hUU, one_mul]
    rwa [hEq] at h
  have hq0 : ∀ x i, 0 ≤ q x i := by
    intro x i
    have h := (hDpsd x).diag_nonneg (i := i)
    rw [Matrix.diagonal_apply_eq] at h
    exact_mod_cast (Complex.le_def.1 h).1
  have hq1 : ∀ x, ∑ i, q x i = 1 := by
    intro x
    have htr : Matrix.trace (ρ x) = Matrix.trace (diagonal (fun i => (q x i : ℂ))) := by
      rw [hq x, mul_assoc, Matrix.trace_mul_comm, mul_assoc, hUU, mul_one]
    rw [(hρ x).2] at htr
    have : ∑ i, (q x i : ℂ) = 1 := by
      rw [htr]; simp [Matrix.trace, Matrix.diag]
    exact_mod_cast this
  set E' : Y → Matrix n n ℂ := fun y => star U * E y * U with hE'def
  have hE' : IsPOVM E' := by
    constructor
    · intro y
      rw [hE'def, Matrix.star_eq_conjTranspose]
      exact (hE.1 y).conjTranspose_mul_mul_same U
    · rw [hE'def]
      simp only
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE.2, mul_one, hUU]
  have hjoint : measJoint p ρ E = measJoint p (fun x => diagonal fun i => (q x i : ℂ)) E' := by
    funext x y
    rw [measJoint, measJoint]
    congr 2
    rw [hq x, mul_assoc, mul_assoc, Matrix.trace_mul_comm]
    congr 1
    simp only [hE'def, mul_assoc]
  have hchi : holevoChi p ρ = holevoChi p (fun x => diagonal fun i => (q x i : ℂ)) := by
    rw [holevoChi, holevoChi]
    have havg : ∑ x, (p x : ℂ) • ρ x
        = U * (∑ x, (p x : ℂ) • diagonal (fun i => (q x i : ℂ))) * star U := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by
        rw [hq x, Matrix.mul_smul, Matrix.smul_mul]
    rw [havg]
    have havg2 : ∑ x, (p x : ℂ) • (diagonal fun i => (q x i : ℂ))
        = diagonal (fun i => ((∑ x, p x * q x i : ℝ) : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.sum_apply]
    rw [havg2, vonNeumannEntropy_unitary_conj_diagonal hU, vonNeumannEntropy_diagonal]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by
      rw [hq x, vonNeumannEntropy_unitary_conj_diagonal hU, vonNeumannEntropy_diagonal]
  rw [hjoint, hchi]
  exact holevo_bound_diagonal p hp0 q hq0 hq1 E' hE'

/-- **The Holevo bound**: the accessible information of a quantum ensemble `{p x, ρ x}` (the
supremum, over all POVMs with outcomes in `Y`, of the mutual information between the label and
the measurement outcome) is at most the Holevo χ quantity of the ensemble.

The ensemble states are assumed to commute (formalized as being simultaneously diagonalizable
by a unitary).  The normalization hypothesis `hp1` on the weights is part of the definition of
an ensemble; the proof in fact never uses it. -/
theorem holevo_bound {X : Type*} [Fintype X] (Y : Type) [Fintype Y] [Nonempty Y]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ρ : X → Matrix n n ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hcomm : SimultaneouslyDiagonalizable ρ) :
    accessibleInfo p ρ Y ≤ holevoChi p ρ := by
  classical
  rw [accessibleInfo]
  refine csSup_le ⟨mutualInfo (measJoint p ρ
    (fun y => if y = Classical.arbitrary Y then 1 else 0)), ?_⟩ ?_
  · refine ⟨_, ⟨fun y => ?_, ?_⟩, rfl⟩
    · by_cases h : y = Classical.arbitrary Y
      · simp only [h, if_pos]
        exact Matrix.PosSemidef.one
      · simp only [h, if_neg, not_false_iff]
        exact Matrix.PosSemidef.zero
    · simp
  · rintro t ⟨E, hE, rfl⟩
    exact holevo_bound_of_POVM p hp0 ρ hρ hcomm E hE

/-! ## Non-vacuity

The hypotheses of `holevo_bound` are satisfiable: here is a concrete qubit ensemble meeting
all of them. -/

/-- The two computational basis states of a qubit. -/
def qubitBasisState (x : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i => if i = x then 1 else 0)

example (x : Fin 2) : IsDensity (qubitBasisState x) := by
  constructor
  · rw [qubitBasisState, Matrix.posSemidef_diagonal_iff]
    intro i; by_cases h : i = x <;> simp [h]
  · simp [qubitBasisState, Matrix.trace, Matrix.diag]

example : SimultaneouslyDiagonalizable qubitBasisState :=
  ⟨1, Submonoid.one_mem _, fun x => ⟨fun i => if i = x then 1 else 0, by
    simp [qubitBasisState, apply_ite (fun r : ℝ => (r : ℂ))]⟩⟩

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

