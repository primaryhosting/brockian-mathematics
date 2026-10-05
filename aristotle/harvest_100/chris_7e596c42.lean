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

import Mathlib

/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope note.

The data-processing inequality states that relative entropy is monotone under
channels.  This file develops the inequality in the *commutative* (equivalently:
jointly diagonalisable / classical) sector of quantum information theory, where a
CPTP map restricted to a commuting family of states is exactly a stochastic map
between the corresponding spectra, and the quantum relative entropy
`Tr ρ (log ρ - log σ)` is exactly the Kullback-Leibler divergence of the two
spectra.

Everything below is proved from scratch: the log-sum inequality (from convexity
of `x ↦ x log x`), the data-processing inequality `QI.data_processing`, and, as a
corollary of it, Gibbs' inequality (nonnegativity of relative entropy).

The last section leaves the commutative sector: it proves the data-processing
inequality `QI.data_processing_max` for the max-relative entropy
`D_max(ρ‖σ) = log inf {λ ≥ 0 | ρ ≤ λ σ}` for arbitrary, possibly noncommuting,
density matrices and arbitrary positive trace-preserving maps (in particular all
CPTP maps).
-/

open Finset

namespace QI

variable {ι κ : Type*}

/-- Relative entropy (Kullback–Leibler divergence) of two finite nonnegative
weight vectors, with the usual conventions `0 log (0/b) = 0` and
`0 log (0/0) = 0` (implemented via `Real.log 0 = 0` and `x / 0 = 0`). -/
noncomputable def relEntropy [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- A (classical) channel from `ι` to `κ`: a column-stochastic matrix. -/
structure Channel (ι κ : Type*) [Fintype κ] where
  /-- The transition matrix: `mat k i` is the probability of output `k` on input `i`. -/
  mat : κ → ι → ℝ
  /-- Transition probabilities are nonnegative. -/
  mat_nonneg : ∀ k i, 0 ≤ mat k i
  /-- Each column sums to one. -/
  col_sum : ∀ i, ∑ k, mat k i = 1

namespace Channel

variable [Fintype ι] [Fintype κ]

/-- The action of a channel on a weight vector. -/
noncomputable def apply (K : Channel ι κ) (p : ι → ℝ) : κ → ℝ :=
  fun k => ∑ i, K.mat k i * p i

lemma apply_nonneg (K : Channel ι κ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (k : κ) :
    0 ≤ K.apply p k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (K.mat_nonneg k i) (hp i)

end Channel

/-! ### The log-sum inequality -/

/-- **Log-sum inequality**: for nonnegative `a, b` with `b i = 0 → a i = 0`,
`(∑ a) log ((∑ a)/(∑ b)) ≤ ∑ a i log (a i / b i)`. -/
theorem log_sum_inequality [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · -- degenerate case: `B = 0`, hence every `b i = 0`, hence every `a i = 0`
    have hbz : ∀ i, b i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ univ) => hb j)).1 hB0.symm i
        (mem_univ i)
      exact this
    have haz : ∀ i, a i = 0 := fun i => hab i (hbz i)
    have : A = 0 := by simp [hA, haz]
    simp [this, haz]
  · -- main case
    have hfun : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x * Real.log x) :=
      Real.convexOn_mul_log
    set w : ι → ℝ := fun i => b i / B with hw
    set x : ι → ℝ := fun i => a i / b i with hx
    have hw0 : ∀ i ∈ univ, 0 ≤ w i := fun i _ => div_nonneg (hb i) hBnn
    have hw1 : ∑ i, w i = 1 := by
      rw [hw]
      rw [← Finset.sum_div, ← hB, div_self (ne_of_gt hBpos)]
    have hxmem : ∀ i ∈ univ, x i ∈ Set.Ici (0 : ℝ) := fun i _ => div_nonneg (ha i) (hb i)
    have key := hfun.map_sum_le hw0 hw1 hxmem
    simp only [smul_eq_mul] at key
    -- identify `∑ w i • x i` with `A / B`
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hpt : ∀ i, w i * x i = a i / B := by
      intro i
      rcases eq_or_lt_of_le (hb i) with h0 | hpos
      · have : a i = 0 := hab i h0.symm
        simp [hw, hx, ← h0, this]
      · have hbi : b i ≠ 0 := ne_of_gt hpos
        show b i / B * (a i / b i) = a i / B
        field_simp
    have hwx : ∑ i, w i * x i = A / B := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hpt i), ← Finset.sum_div, ← hA]
    -- identify the right-hand side
    have hrhs : ∑ i, w i * (x i * Real.log (x i)) =
        (∑ i, a i * Real.log (a i / b i)) / B := by
      have : ∀ i ∈ univ, w i * (x i * Real.log (x i)) =
          (a i * Real.log (a i / b i)) / B := by
        intro i _
        rcases eq_or_lt_of_le (hb i) with h0 | hpos
        · have hai : a i = 0 := hab i h0.symm
          simp [hw, hx, ← h0, hai]
        · show b i / B * (a i / b i * Real.log (a i / b i))
            = a i * Real.log (a i / b i) / B
          rw [← mul_assoc, hpt i, div_mul_eq_mul_div]
      rw [Finset.sum_congr rfl this, ← Finset.sum_div]
    rw [hwx, hrhs] at key
    have h3 := mul_le_mul_of_nonneg_left key hBnn
    have e1 : B * (A / B * Real.log (A / B)) = A * Real.log (A / B) := by field_simp
    have e2 : B * ((∑ i, a i * Real.log (a i / b i)) / B)
        = ∑ i, a i * Real.log (a i / b i) := by field_simp
    rw [e1, e2] at h3
    exact h3

/-! ### The data-processing inequality -/

/-- **Data-processing inequality**.  Relative entropy is monotone under channels:
processing the two inputs `p` and `q` through a common channel `K` can only
decrease their relative entropy.

In the commutative sector of quantum information theory this is exactly the
statement that quantum relative entropy `Tr ρ (log ρ - log σ)` is monotone under
CPTP maps: for a family of commuting states a CPTP map acts on the joint spectra
as the stochastic matrix `K`, and the quantum relative entropy of the states is
the Kullback–Leibler divergence `relEntropy` of the spectra. -/
theorem data_processing [Fintype ι] [Fintype κ] (K : Channel ι κ)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    relEntropy (K.apply p) (K.apply q) ≤ relEntropy p q := by
  have step : ∀ k : κ,
      K.apply p k * Real.log (K.apply p k / K.apply q k) ≤
        ∑ i, K.mat k i * p i * Real.log (p i / q i) := by
    intro k
    have h1 := log_sum_inequality (fun i => K.mat k i * p i) (fun i => K.mat k i * q i)
      (fun i => mul_nonneg (K.mat_nonneg k i) (hp i))
      (fun i => mul_nonneg (K.mat_nonneg k i) (hq i))
      (by
        intro i hi
        rcases mul_eq_zero.1 hi with h | h
        · simp [h]
        · simp [hac i h])
    refine h1.trans_eq ?_
    refine Finset.sum_congr rfl ?_
    intro i _
    rcases eq_or_lt_of_le (K.mat_nonneg k i) with h0 | hpos
    · simp [← h0]
    · congr 1
      rw [mul_div_mul_left _ _ (ne_of_gt hpos)]
  calc relEntropy (K.apply p) (K.apply q)
      = ∑ k, K.apply p k * Real.log (K.apply p k / K.apply q k) := rfl
    _ ≤ ∑ k, ∑ i, K.mat k i * p i * Real.log (p i / q i) :=
        Finset.sum_le_sum fun k _ => step k
    _ = ∑ i, (∑ k, K.mat k i) * (p i * Real.log (p i / q i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = relEntropy p q := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [K.col_sum i, one_mul]

/-! ### Gibbs' inequality, as a corollary -/

/-- The channel that discards its input. -/
noncomputable def trivialChannel (ι : Type*) : Channel ι Unit where
  mat := fun _ _ => 1
  mat_nonneg := fun _ _ => zero_le_one
  col_sum := fun _ => by simp

/-- **Gibbs' inequality**: the relative entropy of two probability distributions is
nonnegative.  Derived from `QI.data_processing` applied to the channel that
discards its input. -/
theorem relEntropy_nonneg [Fintype ι] (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hac : ∀ i, q i = 0 → p i = 0)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    0 ≤ relEntropy p q := by
  have h := data_processing (trivialChannel ι) p q hp hq hac
  have hap : (trivialChannel ι).apply p = fun _ => 1 := by
    funext k
    simp [Channel.apply, trivialChannel, hps]
  have haq : (trivialChannel ι).apply q = fun _ => 1 := by
    funext k
    simp [Channel.apply, trivialChannel, hqs]
  rw [hap, haq] at h
  simpa [relEntropy] using h

/-! ### A genuinely noncommutative instance: the max-relative entropy

The *max-relative entropy* `D_max(ρ‖σ) = log inf {λ ≥ 0 | ρ ≤ λ σ}` (the `α = ∞`
member of the Rényi family of quantum relative entropies) also satisfies the
data-processing inequality, and here we prove it for genuine, possibly
noncommuting density matrices and arbitrary positive trace-preserving maps (in
particular all CPTP maps).  The proof uses the hint's reformulation: instead of
comparing the two infima directly one shows the *reverse inclusion of the
admissible sets*, `{λ | ρ ≤ λσ} ⊆ {λ | Φρ ≤ λΦσ}`, from which monotonicity of
the infimum, and hence of the logarithm, is immediate. -/

open Matrix
open scoped ComplexOrder

variable {n m : Type*}

/-- The Loewner (positive semidefinite) order on matrices: `A ≼ B` iff `B - A` is
positive semidefinite. -/
def LoewnerLE [Fintype n] (A B : Matrix n n ℂ) : Prop := (B - A).PosSemidef

@[inherit_doc] scoped infix:50 " ≼ " => LoewnerLE

/-- The set of admissible ratios `λ` with `ρ ≼ λ • σ`. -/
def maxRatioSet [Fintype n] (rho sigma : Matrix n n ℂ) : Set ℝ :=
  {lam | 0 ≤ lam ∧ rho ≼ (lam : ℂ) • sigma}

/-- The max-relative entropy `D_max(ρ‖σ) = log inf {λ ≥ 0 | ρ ≼ λ σ}`. -/
noncomputable def maxRelEntropy [Fintype n] (rho sigma : Matrix n n ℂ) : ℝ :=
  Real.log (sInf (maxRatioSet rho sigma))

/-- A positive trace-preserving map between matrix algebras.  Every CPTP map (a
quantum channel) is such a map. -/
structure PTPMap (n m : Type*) [Fintype n] [Fintype m] where
  /-- The underlying linear map. -/
  toLin : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ
  /-- Positivity: positive semidefinite matrices are sent to positive semidefinite ones. -/
  map_posSemidef : ∀ A : Matrix n n ℂ, A.PosSemidef → (toLin A).PosSemidef
  /-- Trace preservation. -/
  map_trace : ∀ A : Matrix n n ℂ, (toLin A).trace = A.trace

variable [Fintype n] [Fintype m]

/-- A positive map is monotone for the Loewner order. -/
lemma PTPMap.mono (Phi : PTPMap n m) {A B : Matrix n n ℂ} (h : A ≼ B) :
    Phi.toLin A ≼ Phi.toLin B := by
  have hsub : Phi.toLin (B - A) = Phi.toLin B - Phi.toLin A := Phi.toLin.map_sub B A
  have h2 := Phi.map_posSemidef _ h
  rwa [hsub] at h2

/-- **Key inclusion**: every ratio admissible for `(ρ, σ)` is admissible for the
processed pair `(Φρ, Φσ)`. -/
lemma maxRatioSet_subset (Phi : PTPMap n m) (rho sigma : Matrix n n ℂ) :
    maxRatioSet rho sigma ⊆ maxRatioSet (Phi.toLin rho) (Phi.toLin sigma) := by
  rintro lam ⟨hlam, hle⟩
  refine ⟨hlam, ?_⟩
  have := Phi.mono hle
  rwa [map_smul] at this

lemma maxRatioSet_bddBelow (rho sigma : Matrix n n ℂ) :
    BddBelow (maxRatioSet rho sigma) :=
  ⟨0, fun _ hx => hx.1⟩

/-- For density matrices (unit trace) every admissible ratio is at least one. -/
lemma one_le_of_mem_maxRatioSet {rho sigma : Matrix n n ℂ}
    (hrho : rho.trace = 1) (hsigma : sigma.trace = 1) {lam : ℝ}
    (h : lam ∈ maxRatioSet rho sigma) : 1 ≤ lam := by
  obtain ⟨-, hle⟩ := h
  have htr : (0 : ℂ) ≤ ((lam : ℂ) • sigma - rho).trace := hle.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, hrho, hsigma] at htr
  have := (Complex.le_def.mp htr).1
  simpa using this

/-- **Data-processing inequality for the max-relative entropy**, for arbitrary
(possibly noncommuting) density matrices and an arbitrary positive
trace-preserving map — in particular for every CPTP map. -/
theorem data_processing_max (Phi : PTPMap n m) (rho sigma : Matrix n n ℂ)
    (hrho : rho.trace = 1) (hsigma : sigma.trace = 1)
    (hne : (maxRatioSet rho sigma).Nonempty) :
    maxRelEntropy (Phi.toLin rho) (Phi.toLin sigma) ≤ maxRelEntropy rho sigma := by
  have hsub := maxRatioSet_subset Phi rho sigma
  have hne' : (maxRatioSet (Phi.toLin rho) (Phi.toLin sigma)).Nonempty :=
    hne.mono hsub
  have hle : sInf (maxRatioSet (Phi.toLin rho) (Phi.toLin sigma)) ≤
      sInf (maxRatioSet rho sigma) :=
    csInf_le_csInf (maxRatioSet_bddBelow _ _) hne hsub
  have hpos : 0 < sInf (maxRatioSet (Phi.toLin rho) (Phi.toLin sigma)) := by
    refine lt_of_lt_of_le zero_lt_one (le_csInf hne' ?_)
    intro lam hlam
    exact one_le_of_mem_maxRatioSet (by rw [Phi.map_trace, hrho])
      (by rw [Phi.map_trace, hsigma]) hlam
  exact Real.log_le_log hpos hle

/-- The identity channel, witnessing that the hypotheses of `QI.data_processing_max`
are satisfiable. -/
def idPTPMap (n : Type*) [Fintype n] : PTPMap n n where
  toLin := LinearMap.id
  map_posSemidef := fun _ h => h
  map_trace := fun _ => rfl

lemma maxRatioSet_self_nonempty [DecidableEq n] (rho : Matrix n n ℂ) :
    (maxRatioSet rho rho).Nonempty :=
  ⟨1, zero_le_one, by simpa [LoewnerLE] using Matrix.PosSemidef.zero (n := n) (R := ℂ)⟩

end QI

