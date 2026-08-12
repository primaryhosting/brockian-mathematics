import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- The universal entropy bound produced by an exponentially decaying spectrum
`p i ≤ C * exp (-(c * rank i))`.  It depends only on `C` and `c`, and in particular
*not* on the size of the block, the length of the chain, nor the local dimension. -/
noncomputable def areaLawBound (C c : ℝ) : ℝ :=
  -Real.log (1 - Real.exp (-c)) + c * (C * (Real.exp (-c) / (1 - Real.exp (-c)) ^ 2))

/-! ### Auxiliary estimates -/

/-- Summing a geometric term along an injective ranking gives at most `1`. -/
lemma sum_geometric_rank_le_one {ι : Type*} [Fintype ι] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (rank : ι → ℕ) (hrank : Function.Injective rank) :
    ∑ i, (1 - t) * t ^ (rank i) ≤ 1 := by
  have hsummable : Summable (fun n : ℕ => t ^ n) :=
    summable_geometric_of_lt_one ht0.le ht1
  have h1 : ∑ i, t ^ (rank i) = ∑ n ∈ Finset.image rank Finset.univ, t ^ n := by
    rw [Finset.sum_image (fun a _ b _ h => hrank h)]
  have h2 : ∑ n ∈ Finset.image rank Finset.univ, t ^ n ≤ ∑' n : ℕ, t ^ n :=
    hsummable.sum_le_tsum _ (fun n _ => pow_nonneg ht0.le n)
  have h3 : ∑' n : ℕ, t ^ n = (1 - t)⁻¹ := tsum_geometric_of_lt_one ht0.le ht1
  have ht : (0 : ℝ) < 1 - t := by linarith
  calc ∑ i, (1 - t) * t ^ (rank i) = (1 - t) * ∑ i, t ^ (rank i) := by
        rw [Finset.mul_sum]
    _ ≤ (1 - t) * (1 - t)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        rw [h1, ← h3]; exact h2
    _ = 1 := by field_simp

/-- Gibbs' inequality: the entropy of `p` is bounded by the cross entropy with any
subnormalized positive family `q`. -/
lemma shannonEntropy_le_cross {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hqsum : ∑ i, q i ≤ 1) :
    shannonEntropy p ≤ ∑ i, p i * (-Real.log (q i)) := by
  have key : ∀ i, Real.negMulLog (p i) ≤ p i * (-Real.log (q i)) + (q i - p i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | h0
    · simp [Real.negMulLog, ← h0]
      linarith [(hq i).le]
    · have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hq i) h0)
      have hmul : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog h0.le
      have hdiv : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rw [hdiv] at hmul
      have hsplit : Real.log (q i / p i) = Real.log (q i) - Real.log (p i) :=
        Real.log_div (hq i).ne' h0.ne'
      rw [hsplit] at hmul
      simp only [Real.negMulLog]
      nlinarith [hmul]
  calc shannonEntropy p ≤ ∑ i, (p i * (-Real.log (q i)) + (q i - p i)) :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = (∑ i, p i * (-Real.log (q i))) + ((∑ i, q i) - ∑ i, p i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ ≤ ∑ i, p i * (-Real.log (q i)) := by rw [hpsum]; linarith

/-- With exponentially decaying weights the mean rank is bounded by a constant. -/
lemma sum_rank_le {ι : Type*} [Fintype ι] (p : ι → ℝ) {C t : ℝ} (hC : 0 ≤ C)
    (ht0 : 0 < t) (ht1 : t < 1)
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (hdecay : ∀ i, p i ≤ C * t ^ (rank i)) :
    ∑ i, p i * (rank i : ℝ) ≤ C * (t / (1 - t) ^ 2) := by
  have hsummable : Summable (fun n : ℕ => (n : ℝ) * t ^ n) := by
    have : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 this)
  have hstep : ∑ i, p i * (rank i : ℝ) ≤ ∑ i, C * ((rank i : ℝ) * t ^ (rank i)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := hdecay i
    have hnn : (0 : ℝ) ≤ (rank i : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_pos ht0 (rank i)]
  have h1 : ∑ i, ((rank i : ℝ) * t ^ (rank i))
      = ∑ n ∈ Finset.image rank Finset.univ, (n : ℝ) * t ^ n := by
    rw [Finset.sum_image (fun a _ b _ h => hrank h)]
  have h2 : ∑ n ∈ Finset.image rank Finset.univ, (n : ℝ) * t ^ n
      ≤ ∑' n : ℕ, (n : ℝ) * t ^ n :=
    hsummable.sum_le_tsum _
      (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0.le n))
  have h3 : ∑' n : ℕ, (n : ℝ) * t ^ n = t / (1 - t) ^ 2 := by
    have : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    exact tsum_coe_mul_geometric_of_norm_lt_one this
  calc ∑ i, p i * (rank i : ℝ) ≤ ∑ i, C * ((rank i : ℝ) * t ^ (rank i)) := hstep
    _ = C * ∑ i, ((rank i : ℝ) * t ^ (rank i)) := by rw [Finset.mul_sum]
    _ ≤ C * (t / (1 - t) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC
        rw [h1, ← h3]; exact h2

/-- **Entropy bound from an exponentially decaying spectrum.**
If a probability vector `p` admits an injective ranking along which it decays
exponentially, `p i ≤ C * exp (-(c * rank i))`, then its Shannon entropy is bounded by
a constant depending only on `C` and `c`. -/
theorem shannonEntropy_le_of_exp_decay {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (hdecay : ∀ i, p i ≤ C * Real.exp (-(c * rank i))) :
    shannonEntropy p ≤ areaLawBound C c := by
  set t : ℝ := Real.exp (-c) with ht_def
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by
    rw [ht_def, Real.exp_lt_one_iff]; linarith
  have hpow : ∀ n : ℕ, t ^ n = Real.exp (-(c * n)) := by
    intro n
    rw [ht_def, ← Real.exp_nat_mul]
    ring_nf
  have hdecay' : ∀ i, p i ≤ C * t ^ (rank i) := by
    intro i; rw [hpow]; exact hdecay i
  have hone_sub : (0 : ℝ) < 1 - t := by linarith
  -- the reference distribution
  set q : ι → ℝ := fun i => (1 - t) * t ^ (rank i) with hq_def
  have hqpos : ∀ i, 0 < q i := fun i => mul_pos hone_sub (pow_pos ht0 _)
  have hqsum : ∑ i, q i ≤ 1 := sum_geometric_rank_le_one ht0 ht1 rank hrank
  have hcross := shannonEntropy_le_cross p q hp hpsum hqpos hqsum
  have hlogq : ∀ i, -Real.log (q i) = -Real.log (1 - t) + c * (rank i : ℝ) := by
    intro i
    rw [hq_def]
    simp only
    rw [Real.log_mul hone_sub.ne' (pow_pos ht0 _).ne', Real.log_pow, ht_def, Real.log_exp]
    ring
  have hrewrite : ∑ i, p i * (-Real.log (q i))
      = -Real.log (1 - t) + c * ∑ i, p i * (rank i : ℝ) := by
    have : ∀ i ∈ (Finset.univ : Finset ι),
        p i * (-Real.log (q i))
          = (-Real.log (1 - t)) * p i + c * (p i * (rank i : ℝ)) := by
      intro i _
      rw [hlogq i]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hpsum, mul_one]
  have hmean : ∑ i, p i * (rank i : ℝ) ≤ C * (t / (1 - t) ^ 2) :=
    sum_rank_le p hC ht0 ht1 rank hrank hdecay'
  have : shannonEntropy p ≤ -Real.log (1 - t) + c * (C * (t / (1 - t) ^ 2)) := by
    rw [hrewrite] at hcross
    have := mul_le_mul_of_nonneg_left hmean hc.le
    linarith
  simpa [areaLawBound, ht_def] using this

/-! ## Bipartite pure states, reduced density matrices, entanglement entropy -/

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The reduced density matrix on the `A` factor of a bipartite pure state
`psi : A → B → ℂ` (given as its matrix of coefficients in a product basis). -/
noncomputable def reducedDensity (psi : A → B → ℂ) : Matrix A A ℂ :=
  (Matrix.of psi) * (Matrix.of psi).conjTranspose

omit [Fintype A] in
lemma reducedDensity_apply (psi : A → B → ℂ) (a a' : A) :
    reducedDensity psi a a' = ∑ b, psi a b * (starRingEnd ℂ) (psi a' b) := by
  simp [reducedDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Reduced density matrices are positive semidefinite. -/
lemma reducedDensity_posSemidef (psi : A → B → ℂ) : (reducedDensity psi).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- The Schmidt spectrum of a bipartite pure state across the given cut: the
eigenvalues of the reduced density matrix. -/
noncomputable def schmidtSpectrum [DecidableEq A] (psi : A → B → ℂ) : A → ℝ :=
  (reducedDensity_posSemidef psi).isHermitian.eigenvalues

lemma schmidtSpectrum_nonneg [DecidableEq A] (psi : A → B → ℂ) (a : A) :
    0 ≤ schmidtSpectrum psi a :=
  (reducedDensity_posSemidef psi).eigenvalues_nonneg a

/-- For a normalized state the Schmidt spectrum is a probability vector. -/
lemma sum_schmidtSpectrum [DecidableEq A] (psi : A → B → ℂ)
    (hnorm : ∑ a, ∑ b, ‖psi a b‖ ^ 2 = 1) :
    ∑ a, schmidtSpectrum psi a = 1 := by
  have htr : (reducedDensity psi).trace = ∑ a, ((schmidtSpectrum psi a : ℝ) : ℂ) :=
    (reducedDensity_posSemidef psi).isHermitian.trace_eq_sum_eigenvalues
  have htr2 : (reducedDensity psi).trace = ((1 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    have : ∀ a : A, reducedDensity psi a a = ((∑ b, ‖psi a b‖ ^ 2 : ℝ) : ℂ) := by
      intro a
      rw [reducedDensity_apply]
      push_cast
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Complex.ofReal_sum, hnorm]
  rw [htr2] at htr
  have : ((∑ a, schmidtSpectrum psi a : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]; exact htr.symm
  exact_mod_cast this

/-- Entanglement entropy of a bipartite pure state: the von Neumann entropy of its
reduced density matrix. -/
noncomputable def entanglementEntropy [DecidableEq A] (psi : A → B → ℂ) : ℝ :=
  shannonEntropy (schmidtSpectrum psi)

/-! ## One-dimensional spin chains -/

/-- Configurations of a chain of `N` sites with local dimension `d`. -/
abbrev Config (N d : ℕ) := Fin N → Fin d

/-- Configurations of the left block `{i < L}` of the chain. -/
abbrev LeftConfig (N d L : ℕ) := {i : Fin N // (i : ℕ) < L} → Fin d

/-- Configurations of the right block `{i ≥ L}` of the chain. -/
abbrev RightConfig (N d L : ℕ) := {i : Fin N // ¬ (i : ℕ) < L} → Fin d

/-- Splitting the chain at position `L` into left and right blocks. -/
def cutEquiv (N d L : ℕ) : Config N d ≃ LeftConfig N d L × RightConfig N d L :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin N => (i : ℕ) < L) (fun _ => Fin d)

/-- A state of the chain viewed as a bipartite state across the cut at `L`. -/
def cutState {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ) :
    LeftConfig N d L → RightConfig N d L → ℂ :=
  fun a b => psi ((cutEquiv N d L).symm (a, b))

/-- Entanglement entropy of a chain state across the cut at position `L`. -/
noncomputable def cutEntropy {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ) : ℝ :=
  entanglementEntropy (cutState psi L)

/-- The Schmidt spectrum of a chain state across the cut at position `L`. -/
noncomputable def cutSpectrum {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ) :
    LeftConfig N d L → ℝ :=
  schmidtSpectrum (cutState psi L)

lemma sum_norm_cutState {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ)
    (hnorm : ∑ x, ‖psi x‖ ^ 2 = 1) :
    ∑ a, ∑ b, ‖cutState psi L a b‖ ^ 2 = 1 := by
  rw [← hnorm]
  calc ∑ a, ∑ b, ‖cutState psi L a b‖ ^ 2
      = ∑ p : LeftConfig N d L × RightConfig N d L, ‖cutState psi L p.1 p.2‖ ^ 2 :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ x, ‖psi x‖ ^ 2 :=
        Fintype.sum_equiv (cutEquiv N d L).symm _ _ (fun p => rfl)

/-- Normalized chain states have a probability vector as Schmidt spectrum across any cut. -/
lemma sum_cutSpectrum {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ)
    (hnorm : ∑ x, ‖psi x‖ ^ 2 = 1) :
    ∑ a, cutSpectrum psi L a = 1 :=
  sum_schmidtSpectrum _ (sum_norm_cutState psi L hnorm)

/-- **Exponential decay of the Schmidt spectrum across a cut.**  This is the property that
Hastings' analysis extracts from a spectral gap: the Schmidt coefficients of a gapped
ground state across a cut, arranged in decreasing order, decay exponentially with
rate `c` and prefactor `C` (both determined by the gap, the interaction strength and the
local dimension, but *not* by the length of the chain or the position of the cut). -/
def ExpSchmidtDecay {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ) (C c : ℝ) : Prop :=
  ∃ rank : LeftConfig N d L → ℕ, Function.Injective rank ∧
    ∀ a, cutSpectrum psi L a ≤ C * Real.exp (-(c * rank a))

/-- The exponential-decay hypothesis is never vacuous: for a *fixed* finite chain and a
fixed cut, some pair of constants always works (with `C` growing with the dimension of
the block).  The mathematical content of the area law therefore lies in the *uniformity*
of the constants `C, c` over all chain lengths and all cut positions, which is what
`Phys.area_law_1d_uniform` below expresses. -/
lemma expSchmidtDecay_of_fintype {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ)
    (hnorm : ∑ x, ‖psi x‖ ^ 2 = 1) {c : ℝ} (hc : 0 < c) :
    ExpSchmidtDecay psi L (Real.exp (c * (Fintype.card (LeftConfig N d L) : ℝ))) c := by
  classical
  refine ⟨fun a => ((Fintype.equivFin (LeftConfig N d L)) a : ℕ), ?_, ?_⟩
  · intro a a' h
    exact (Fintype.equivFin (LeftConfig N d L)).injective (Fin.ext h)
  · intro a
    have hle1 : cutSpectrum psi L a ≤ 1 := by
      rw [← sum_cutSpectrum psi L hnorm]
      exact Finset.single_le_sum (f := cutSpectrum psi L)
        (fun i _ => schmidtSpectrum_nonneg _ i) (Finset.mem_univ a)
    have hrank : (((Fintype.equivFin (LeftConfig N d L)) a : ℕ) : ℝ)
        ≤ (Fintype.card (LeftConfig N d L) : ℝ) := by
      exact_mod_cast ((Fintype.equivFin (LeftConfig N d L)) a).isLt.le
    have : (1 : ℝ) ≤ Real.exp (c * (Fintype.card (LeftConfig N d L) : ℝ))
        * Real.exp (-(c * (((Fintype.equivFin (LeftConfig N d L)) a : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      rw [Real.one_le_exp_iff]
      nlinarith
    linarith

/-- **Area law for gapped ground states in one dimension.**

For a normalized state `psi` of a one-dimensional chain of `N` sites with local
dimension `d`, whose Schmidt spectrum across the cut at position `L` decays
exponentially with constants `C, c` (the property produced by a spectral gap in
Hastings' theorem), the entanglement entropy across the cut is bounded by
`areaLawBound C c`.

The bound depends only on `C` and `c`; it is independent of the chain length `N`,
the local dimension `d` and, crucially, of the size `L` of the block.  This is exactly
the one-dimensional area law: entropy of a block is bounded by a constant, rather than
growing with the block's volume. -/
theorem area_law_1d {N d : ℕ} (psi : Config N d → ℂ) (L : ℕ)
    (hnorm : ∑ x, ‖psi x‖ ^ 2 = 1) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hdecay : ExpSchmidtDecay psi L C c) :
    cutEntropy psi L ≤ areaLawBound C c := by
  obtain ⟨rank, hrank, hd⟩ := hdecay
  exact shannonEntropy_le_of_exp_decay (cutSpectrum psi L)
    (fun a => schmidtSpectrum_nonneg _ a) (sum_cutSpectrum psi L hnorm) hC hc rank hrank hd

/-- `psi` is a normalized ground state of the Hamiltonian `H` with energy `E` and
spectral gap `gap`: it is an eigenvector of energy `E`, and every state orthogonal to it
has energy at least `E + gap`. -/
def IsGroundStateWithGap {N d : ℕ} (H : Matrix (Config N d) (Config N d) ℂ)
    (psi : Config N d → ℂ) (E gap : ℝ) : Prop :=
  H.IsHermitian ∧ (∑ x, ‖psi x‖ ^ 2 = 1) ∧ H.mulVec psi = (E : ℂ) • psi ∧ 0 < gap ∧
    ∀ phi : Config N d → ℂ, (∑ x, (starRingEnd ℂ) (psi x) * phi x) = 0 →
      ((E + gap) * ∑ x, ‖phi x‖ ^ 2 : ℝ)
        ≤ (∑ x, (starRingEnd ℂ) (phi x) * H.mulVec phi x).re

/-- The notion of a gapped ground state is not vacuous: on any chain there is a
Hamiltonian with a normalized ground state separated by a gap. -/
lemma exists_gapped_ground_state {N d : ℕ} (c0 : Config N d) :
    ∃ (H : Matrix (Config N d) (Config N d) ℂ) (psi : Config N d → ℂ) (E gap : ℝ),
      IsGroundStateWithGap H psi E gap := by
  classical
  refine ⟨Matrix.diagonal (fun x => if x = c0 then (0 : ℂ) else 1),
    (fun x => if x = c0 then (1 : ℂ) else 0), 0, 1, ?_, ?_, ?_, one_pos, ?_⟩
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    by_cases h : i = c0 <;> simp [h, IsSelfAdjoint]
  · simp [apply_ite norm]
  · funext x
    rw [Matrix.mulVec_diagonal]
    by_cases h : x = c0 <;> simp [h]
  · intro phi hphi
    have hc0 : phi c0 = 0 := by simpa using hphi
    have hterm : ∀ x : Config N d,
        (starRingEnd ℂ) (phi x)
            * (Matrix.diagonal (fun y => if y = c0 then (0 : ℂ) else 1)).mulVec phi x
          = (((‖phi x‖ ^ 2 : ℝ) : ℂ)) := by
      intro x
      rw [Matrix.mulVec_diagonal]
      by_cases h : x = c0
      · simp [h, hc0]
      · rw [if_neg h, one_mul, mul_comm, Complex.mul_conj]
        norm_cast
        exact Complex.normSq_eq_norm_sq _
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Complex.ofReal_sum, Complex.ofReal_re]
    simp

/-- **Area law for a gapped ground state of a one-dimensional chain.**

This is the physics statement in its usual form: for a gapped local Hamiltonian on a
spin chain, the entanglement entropy of the ground state across any cut is bounded by a
constant independent of the block size and of the chain length.

The spectral gap enters through the hypothesis `hastings`: the analytic heart of
Hastings' theorem is precisely the statement that a spectral gap forces the Schmidt
spectrum across every cut to decay exponentially with constants `C, c` that are uniform
in the chain length and the cut position.  That implication is *assumed* here; what is
proved is that it entails the area law, with the explicit universal constant
`Phys.areaLawBound C c`. -/
theorem area_law_1d_gapped {N d : ℕ} (H : Matrix (Config N d) (Config N d) ℂ)
    (psi : Config N d → ℂ) (E gap : ℝ)
    (hstate : IsGroundStateWithGap H psi E gap)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hastings : ∀ L : ℕ, ExpSchmidtDecay psi L C c) :
    ∀ L : ℕ, cutEntropy psi L ≤ areaLawBound C c :=
  fun L => area_law_1d psi L hstate.2.1 hC hc (hastings L)

/-- The area-law bound is uniform: a single constant works simultaneously for every
chain length, every local dimension and every cut position, as long as the
exponential decay constants `C, c` are uniform. -/
theorem area_law_1d_uniform {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ (N d : ℕ) (psi : Config N d → ℂ) (L : ℕ), (∑ x, ‖psi x‖ ^ 2 = 1) →
      ExpSchmidtDecay psi L C c → cutEntropy psi L ≤ areaLawBound C c :=
  fun _ _ psi L hnorm hdecay => area_law_1d psi L hnorm hC hc hdecay

end Phys

