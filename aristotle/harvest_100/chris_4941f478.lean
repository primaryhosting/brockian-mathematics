import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/
noncomputable def s : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma s_mul_s : s * s = 1 / 2 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  unfold s
  rw [← Complex.ofReal_mul, h]
  norm_num

@[simp] lemma conj_s : (starRingEnd ℂ) s = s := Complex.conj_ofReal _

/-- A single-qubit vector. -/
abbrev Vec2 := Fin 2 → ℂ

/-- A two-qubit vector, indexed by pairs of qubit indices. -/
abbrev Vec4 := Fin 2 × Fin 2 → ℂ

/-- `|0⟩`. -/
def ket0 : Vec2 := ![1, 0]
/-- `|1⟩`. -/
def ket1 : Vec2 := ![0, 1]
/-- `|+⟩ = (|0⟩+|1⟩)/√2`. -/
noncomputable def ketP : Vec2 := ![s, s]
/-- `|-⟩ = (|0⟩-|1⟩)/√2`. -/
noncomputable def ketM : Vec2 := ![s, -s]

/-- The tensor product of two single-qubit vectors. -/
def tens (u v : Vec2) : Vec4 := fun x => u x.1 * v x.2

/-- The Hermitian inner product on two-qubit vectors, conjugate-linear in the
first argument. -/
noncomputable def ip (u v : Vec4) : ℂ := ∑ x : Fin 2 × Fin 2, (starRingEnd ℂ) (u x) * v x

/-- The four vectors of the PBR entangled measurement basis. -/
noncomputable def xi : Fin 4 → Vec4 :=
  ![fun x => s * (tens ket0 ket1 x + tens ket1 ket0 x),
    fun x => s * (tens ket0 ketM x + tens ket1 ketP x),
    fun x => s * (tens ketP ket1 x + tens ketM ket0 x),
    fun x => s * (tens ketP ketM x + tens ketM ketP x)]

/-- The preparation used in the PBR argument: `prep 0 = |0⟩`, `prep 1 = |+⟩`. -/
noncomputable def prep : Fin 2 → Vec2 := ![ket0, ketP]

/-- The pair of preparations which the `i`-th measurement outcome excludes. -/
def badPair : Fin 4 → Fin 2 × Fin 2 := ![(0, 0), (0, 1), (1, 0), (1, 1)]

/-- Born rule probability of outcome `i` for the product preparation `(a, b)`. -/
noncomputable def bornProb (i : Fin 4) (a b : Fin 2) : ℝ :=
  Complex.normSq (ip (xi i) (tens (prep a) (prep b)))

section Computation

private lemma expand (u v : Vec4) :
    ip u v = (starRingEnd ℂ) (u (0, 0)) * v (0, 0) + (starRingEnd ℂ) (u (0, 1)) * v (0, 1)
      + ((starRingEnd ℂ) (u (1, 0)) * v (1, 0) + (starRingEnd ℂ) (u (1, 1)) * v (1, 1)) := by
  simp [ip, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Each of the four PBR basis vectors is orthogonal to the corresponding product
preparation: the outcome `i` never occurs on the preparation `badPair i`. -/
theorem born_bad (i : Fin 4) : bornProb i (badPair i).1 (badPair i).2 = 0 := by
  fin_cases i <;>
    (simp [bornProb, badPair, xi, prep, tens, ket0, ket1, ketP, ketM, expand]; try ring_nf)

lemma sqrt2_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma sqrt2_inv_pow4 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 4 = 1 / 4 := by
  have : ((Real.sqrt 2)⁻¹ : ℝ) ^ 4 = (((Real.sqrt 2)⁻¹ : ℝ) ^ 2) ^ 2 := by ring
  rw [this, sqrt2_inv_sq]; norm_num

@[simp] lemma s_re : s.re = (Real.sqrt 2)⁻¹ := rfl

@[simp] lemma s_im : s.im = 0 := rfl

lemma s_sq : s ^ 2 = 1 / 2 := by rw [pow_two, s_mul_s]

lemma s_pow3 : s ^ 3 = s / 2 := by
  have : s ^ 3 = s * (s * s) := by ring
  rw [this, s_mul_s]; ring

lemma s_pow4 : s ^ 4 = 1 / 4 := by
  have : s ^ 4 = (s * s) * (s * s) := by ring
  rw [this, s_mul_s]; norm_num

lemma s_pow6 : s ^ 6 = 1 / 8 := by
  have : s ^ 6 = (s * s) * ((s * s) * (s * s)) := by ring
  rw [this, s_mul_s]; norm_num

lemma sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma sqrt2_pow4 : (Real.sqrt 2) ^ 4 = 4 := by
  have : (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
  rw [this, sqrt2_sq]; norm_num

lemma sqrt2_pow6 : (Real.sqrt 2) ^ 6 = 8 := by
  have : (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
  rw [this, sqrt2_sq]; norm_num

lemma sqrt2_pow8 : (Real.sqrt 2) ^ 8 = 16 := by
  have : (Real.sqrt 2) ^ 8 = ((Real.sqrt 2) ^ 2) ^ 4 := by ring
  rw [this, sqrt2_sq]; norm_num

/-- Normalising tactic for the explicit amplitude computations. -/
local macro "pbr_calc" : tactic =>
  `(tactic| (ring_nf;
             try simp [s_sq, s_pow3, s_pow4, s_pow6, sqrt2_inv_sq, sqrt2_inv_pow4,
                       sqrt2_sq, sqrt2_pow4, sqrt2_pow6, sqrt2_pow8];
             try ring_nf;
             try norm_num))

/-- The four PBR vectors are orthonormal, so they really do form a measurement
basis of the two-qubit space. -/
theorem xi_orthonormal (i j : Fin 4) : ip (xi i) (xi j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [xi, tens, ket0, ket1, ketP, ketM, expand] <;> pbr_calc

/-- Completeness of the PBR measurement on the four product preparations: the four
outcome probabilities sum to one. -/
theorem born_sum (a b : Fin 2) : ∑ i, bornProb i a b = 1 := by
  fin_cases a <;> fin_cases b <;>
    simp [bornProb, Fin.sum_univ_four, xi, prep, tens, ket0, ket1, ketP, ketM, expand,
      Complex.normSq_apply] <;> pbr_calc

/-- Sanity check: the probabilities are not all zero, e.g. outcome `1` on the
preparation `|0⟩ ⊗ |+⟩` has probability `1/4`. -/
theorem born_example : bornProb 0 0 1 = 1 / 4 := by
  simp [bornProb, xi, prep, tens, ket0, ket1, ketP, ketM, expand, Complex.normSq_apply]
  pbr_calc

end Computation

/-! ## Ontological models with preparation independence -/

/-- An ontological (hidden variable) model for the two preparations `|0⟩` and `|+⟩`,
satisfying the PBR preparation independence assumption: the ontic state of two
independently prepared systems is a pair `(λ₁, λ₂)` distributed according to the
product of the individual distributions. -/
structure OnticModel (Λ : Type) [Fintype Λ] where
  /-- `mu a` is the probability distribution over ontic states of preparation `prep a`. -/
  mu : Fin 2 → Λ → ℝ
  mu_nonneg : ∀ a l, 0 ≤ mu a l
  mu_sum : ∀ a, ∑ l, mu a l = 1
  /-- `resp i (l₁, l₂)` is the probability that the PBR measurement returns outcome `i`
  when the joint ontic state is `(l₁, l₂)`. -/
  resp : Fin 4 → Λ × Λ → ℝ
  resp_nonneg : ∀ i p, 0 ≤ resp i p
  resp_sum : ∀ p, ∑ i, resp i p = 1
  /-- The model reproduces the quantum (Born rule) statistics, with preparation
  independence built into the product form of the joint distribution. -/
  born : ∀ (i : Fin 4) (a b : Fin 2),
    ∑ p : Λ × Λ, mu a p.1 * mu b p.2 * resp i p = bornProb i a b

/-- The hypotheses of `OnticModel` are consistent: quantum theory itself provides
such a model, in which the ontic state simply *is* the quantum state.  (Of course
this model has disjoint supports, in accordance with `pbr_theorem`.) -/
noncomputable def quantumModel : OnticModel (Fin 2) where
  mu a l := if a = l then 1 else 0
  mu_nonneg := by intro a l; split <;> norm_num
  mu_sum := by intro a; simp
  resp i p := bornProb i p.1 p.2
  resp_nonneg := by intro i p; exact Complex.normSq_nonneg _
  resp_sum := by intro p; exact born_sum p.1 p.2
  born := by
    intro i a b
    fin_cases a <;> fin_cases b <;>
      simp [Fintype.sum_prod_type]

variable {Λ : Type} [Fintype Λ]

private lemma resp_zero_of_pos (M : OnticModel Λ) (l : Λ) (h0 : 0 < M.mu 0 l)
    (h1 : 0 < M.mu 1 l) (i : Fin 4) : M.resp i (l, l) = 0 := by
  set a := (badPair i).1 with ha
  set b := (badPair i).2 with hb
  have hsum : ∑ p : Λ × Λ, M.mu a p.1 * M.mu b p.2 * M.resp i p = 0 := by
    rw [M.born i a b, ha, hb, born_bad i]
  have hterm : M.mu a l * M.mu b l * M.resp i (l, l) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
      mul_nonneg (mul_nonneg (M.mu_nonneg a p.1) (M.mu_nonneg b p.2)) (M.resp_nonneg i p))).1
      hsum (l, l) (Finset.mem_univ _)
    simpa using this
  have hpos : 0 < M.mu a l * M.mu b l := by
    have ha' : 0 < M.mu a l := by fin_cases i <;> simp [ha, badPair] <;> assumption
    have hb' : 0 < M.mu b l := by fin_cases i <;> simp [hb, badPair] <;> assumption
    exact mul_pos ha' hb'
  rcases mul_eq_zero.1 hterm with h | h
  · exact absurd h (ne_of_gt hpos)
  · exact h

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of quantum theory
that reproduces the Born-rule statistics of the PBR entangled measurement and
satisfies preparation independence, the distributions of ontic states associated
with the distinct pure states `|0⟩` and `|+⟩` have disjoint supports: no ontic
state `l` is compatible with both preparations.  Hence the quantum state is ontic:
it is a function of the ontic state. -/
theorem pbr_theorem (M : OnticModel Λ) (l : Λ) : M.mu 0 l * M.mu 1 l = 0 := by
  by_contra h
  have h0 : 0 < M.mu 0 l := lt_of_le_of_ne (M.mu_nonneg 0 l)
    (fun hh => h (by rw [← hh]; ring))
  have h1 : 0 < M.mu 1 l := lt_of_le_of_ne (M.mu_nonneg 1 l)
    (fun hh => h (by rw [← hh]; ring))
  have : (1 : ℝ) = 0 := by
    rw [← M.resp_sum (l, l)]
    exact Finset.sum_eq_zero fun i _ => resp_zero_of_pos M l h0 h1 i
  exact one_ne_zero this

/-- Restatement of the PBR conclusion: an ontic state that can occur for the
preparation `|0⟩` never occurs for the preparation `|+⟩`.  Thus the pure quantum
state is a function of the ontic state, i.e. it is ontic rather than epistemic. -/
theorem pbr_supports_disjoint (M : OnticModel Λ) (l : Λ)
    (h : M.mu 0 l ≠ 0) : M.mu 1 l = 0 := by
  rcases mul_eq_zero.1 (pbr_theorem M l) with h0 | h1
  · exact absurd h0 h
  · exact h1

end QI

#print axioms QI.pbr_theorem
#print axioms QI.born_bad
#print axioms QI.xi_orthonormal
#print axioms QI.born_sum

