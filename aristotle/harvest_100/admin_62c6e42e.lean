import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `M_n(ℂ)`: a unital positive linear functional.
Positivity is expressed by requiring `f (Xᴴ * X)` to be a nonnegative real number. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  pos : ∀ X : Matrix n n ℂ, ∃ r : ℝ, 0 ≤ r ∧ f (Xᴴ * X) = (r : ℂ)

/-- `f` extends the pure state `d ↦ d i` of the diagonal MASA `D_n ⊆ M_n(ℂ)`.
(The pure states of the commutative algebra `D_n ≃ ℂ^n` are exactly the evaluations.) -/
def ExtendsDiagonalPureState (i : n) (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ d : n → ℂ, f (Matrix.diagonal d) = d i

/-- The functional `A ↦ A i i` on `M_n(ℂ)`. -/
def entryFunctional (i : n) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun A := A i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] lemma entryFunctional_apply (i : n) (A : Matrix n n ℂ) :
    entryFunctional i A = A i i := rfl

/-! ### Elementary preliminaries -/

/-- If an affine function `t ↦ c + t * m` of a real parameter only takes nonnegative real
values, then its slope `m` vanishes. -/
lemma slope_eq_zero_of_nonneg {c m : ℂ}
    (h : ∀ t : ℝ, ∃ r : ℝ, 0 ≤ r ∧ c + (t : ℂ) * m = (r : ℂ)) : m = 0 := by
  obtain ⟨r₀, hr₀, h₀⟩ := h 0
  obtain ⟨r₁, hr₁, h₁⟩ := h 1
  have hc : c = (r₀ : ℂ) := by simpa using h₀
  have hm : m = ((r₁ - r₀ : ℝ) : ℂ) := by
    have : (r₀ : ℂ) + m = (r₁ : ℂ) := by simpa [hc] using h₁
    push_cast
    linear_combination this
  set a : ℝ := r₁ - r₀ with ha
  by_contra hne
  have ha0 : a ≠ 0 := by
    intro h'
    exact hne (by simp [hm, h'])
  obtain ⟨r, hr, hEq⟩ := h (-(r₀ + 1) / a)
  rw [hc, hm] at hEq
  have hEqR : r₀ + (-(r₀ + 1) / a) * a = r := by exact_mod_cast hEq
  rw [div_mul_cancel₀ _ ha0] at hEqR
  linarith

/-- Expansion of an arbitrary linear functional on matrices in the matrix units. -/
lemma linearMap_apply_eq_sum (f : Matrix n n ℂ →ₗ[ℂ] ℂ) (A : Matrix n n ℂ) :
    f A = ∑ q : n, ∑ s : n, A q s * f (Matrix.single q s 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : Matrix.single q s (A q s) = A q s • Matrix.single q s (1 : ℂ) := by
    simp
  rw [this, map_smul, smul_eq_mul]

/-- For a rank-one matrix built from a vector `w`, `Xᴴ * X` is the outer product. -/
lemma conjTranspose_mul_self_vecMulVec (k : n) (w : n → ℂ) :
    (Matrix.vecMulVec (Pi.single k (1 : ℂ)) w)ᴴ * (Matrix.vecMulVec (Pi.single k 1) w)
      = Matrix.vecMulVec (star w) w := by
  ext q s
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    Pi.star_apply]
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ### The core computation -/

section Core

variable {f : Matrix n n ℂ →ₗ[ℂ] ℂ}

/-- Positivity of a state, evaluated on a rank-one matrix supported on two coordinates. -/
lemma state_pos_pair (hf : IsState f) {k l : n} (hkl : k ≠ l) (α β : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (starRingEnd ℂ) α * α * f (Matrix.single k k 1)
        + (starRingEnd ℂ) α * β * f (Matrix.single k l 1)
        + (starRingEnd ℂ) β * α * f (Matrix.single l k 1)
        + (starRingEnd ℂ) β * β * f (Matrix.single l l 1) = (r : ℂ) := by
  classical
  set w : n → ℂ := fun x => if x = k then α else if x = l then β else 0 with hw
  have hwk : w k = α := by simp [hw]
  have hwl : w l = β := by simp [hw, Ne.symm hkl]
  obtain ⟨r, hr, hval⟩ := hf.pos (Matrix.vecMulVec (Pi.single k (1 : ℂ)) w)
  rw [conjTranspose_mul_self_vecMulVec] at hval
  refine ⟨r, hr, ?_⟩
  have hstep : ∀ q : n, ∑ s : n, Matrix.vecMulVec (star w) w q s * f (Matrix.single q s 1)
      = (starRingEnd ℂ) (w q) * (w k * f (Matrix.single q k 1)
          + w l * f (Matrix.single q l 1)) := by
    intro q
    have hterm : ∀ s : n, Matrix.vecMulVec (star w) w q s * f (Matrix.single q s 1)
        = (starRingEnd ℂ) (w q) * (w s * f (Matrix.single q s 1)) := by
      intro s
      simp [Matrix.vecMulVec_apply, mul_assoc]
    rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ ({k, l} : Finset n))]
    · rw [Finset.sum_pair hkl]
    · intro s _ hs
      have hsk : s ≠ k := by intro h; exact hs (by simp [h])
      have hsl : s ≠ l := by intro h; exact hs (by simp [h])
      simp [hw, hsk, hsl]
  have key : f (Matrix.vecMulVec (star w) w)
      = (starRingEnd ℂ) α * α * f (Matrix.single k k 1)
        + (starRingEnd ℂ) α * β * f (Matrix.single k l 1)
        + (starRingEnd ℂ) β * α * f (Matrix.single l k 1)
        + (starRingEnd ℂ) β * β * f (Matrix.single l l 1) := by
    rw [linearMap_apply_eq_sum f, Finset.sum_congr rfl fun q _ => hstep q,
      ← Finset.sum_subset (Finset.subset_univ ({k, l} : Finset n))]
    · rw [Finset.sum_pair hkl, hwk, hwl]
      ring
    · intro q _ hq
      have hqk : q ≠ k := by intro h; exact hq (by simp [h])
      have hql : q ≠ l := by intro h; exact hq (by simp [h])
      simp [hw, hqk, hql]
  rw [← key]
  exact hval

/-- If a matrix unit `E k k` is annihilated by the state, so are the off-diagonal units
`E k l` and `E l k`. -/
lemma offdiag_eq_zero (hf : IsState f) {k l : n} (hkl : k ≠ l)
    (hkk : f (Matrix.single k k 1) = 0) :
    f (Matrix.single k l 1) = 0 ∧ f (Matrix.single l k 1) = 0 := by
  set u : ℂ := f (Matrix.single k l 1) with hu
  set v : ℂ := f (Matrix.single l k 1) with hv
  set c : ℂ := f (Matrix.single l l 1) with hc
  have h1 : u + v = 0 := by
    refine slope_eq_zero_of_nonneg (c := c) ?_
    intro t
    obtain ⟨r, hr, hEq⟩ := state_pos_pair hf hkl (t : ℂ) 1
    refine ⟨r, hr, ?_⟩
    rw [← hEq, hkk]
    simp only [map_one, Complex.conj_ofReal, ← hu, ← hv, ← hc]
    ring
  have h2 : Complex.I * (v - u) = 0 := by
    refine slope_eq_zero_of_nonneg (c := c) ?_
    intro t
    obtain ⟨r, hr, hEq⟩ := state_pos_pair hf hkl ((t : ℂ) * Complex.I) 1
    refine ⟨r, hr, ?_⟩
    rw [← hEq, hkk]
    simp only [map_one, map_mul, Complex.conj_ofReal, Complex.conj_I, ← hu, ← hv, ← hc]
    ring
  have h3 : v - u = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  exact ⟨by linear_combination (h1 - h3) / 2, by linear_combination (h1 + h3) / 2⟩

end Core

/-! ### Pure states of the diagonal MASA -/

/-- The pure states of the commutative algebra `D_n ≃ ℂ^n` (equivalently, its characters:
unital multiplicative linear functionals) are exactly the coordinate evaluations
`d ↦ d i`.  This justifies the definition of `Frontier.ExtendsDiagonalPureState`. -/
theorem diagonal_character_eq_eval (chi : (n → ℂ) →ₗ[ℂ] ℂ)
    (hmul : ∀ a b : n → ℂ, chi (a * b) = chi a * chi b) (hone : chi 1 = 1) :
    ∃ i : n, ∀ d : n → ℂ, chi d = d i := by
  classical
  have hidem : ∀ k : n, chi (Pi.single k (1 : ℂ)) * chi (Pi.single k (1 : ℂ))
      = chi (Pi.single k (1 : ℂ)) := by
    intro k
    rw [← hmul]
    congr 1
    funext x
    by_cases h : k = x <;> simp [Pi.single_apply, h]
  have hsum : ∑ k : n, chi (Pi.single k (1 : ℂ)) = 1 := by
    have hone' : ∑ k : n, (Pi.single k (1 : ℂ) : n → ℂ) = (1 : n → ℂ) := by
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← map_sum, hone', hone]
  have hex : ∃ i : n, chi (Pi.single i (1 : ℂ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_congr rfl fun k _ => hcon k] at hsum
    simp at hsum
  obtain ⟨i, hi⟩ := hex
  have hi1 : chi (Pi.single i (1 : ℂ)) = 1 :=
    mul_right_cancel₀ hi (by rw [hidem i, one_mul])
  have hzero : ∀ k : n, k ≠ i → chi (Pi.single k (1 : ℂ)) = 0 := by
    intro k hk
    have hprod : chi (Pi.single k (1 : ℂ)) * chi (Pi.single i (1 : ℂ)) = 0 := by
      rw [← hmul]
      have hmul0 : (Pi.single k (1 : ℂ) : n → ℂ) * (Pi.single i (1 : ℂ) : n → ℂ) = 0 := by
        funext x
        by_cases h : k = x
        · subst h
          simp [Ne.symm hk]
        · simp [Pi.single_apply, h]
      rw [hmul0, map_zero]
    rw [hi1, mul_one] at hprod
    exact hprod
  refine ⟨i, fun d => ?_⟩
  have hexp : chi d = ∑ k : n, d k * chi (Pi.single k (1 : ℂ)) := by
    conv_lhs => rw [← Finset.univ_sum_single d]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsm : (Pi.single k (d k) : n → ℂ) = d k • (Pi.single k (1 : ℂ) : n → ℂ) := by
      funext x
      by_cases h : k = x <;> simp [Pi.single_apply, h]
    rw [hsm, map_smul, smul_eq_mul]
  rw [hexp, Finset.sum_eq_single i]
  · rw [hi1, mul_one]
  · intro k _ hk
    rw [hzero k hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### The finite-dimensional Kadison–Singer theorem -/

/-- **Kadison–Singer, finite-dimensional case (base case).**
For each index `i`, the pure state `d ↦ d i` of the diagonal MASA `D_n ⊆ M_n(ℂ)` has a
*unique* extension to a state on the full matrix algebra `M_n(ℂ)`, namely `A ↦ A i i`.

This is the finite-dimensional instance of the Kadison–Singer problem (whose full,
infinite-dimensional form, for the atomic MASA `ℓ^∞(ℕ) ⊆ B(ℓ²(ℕ))`, was resolved by
Marcus–Spielman–Srivastava). -/
theorem kadison_singer (i : n) :
    ∃! f : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState f ∧ ExtendsDiagonalPureState i f := by
  refine ⟨entryFunctional i, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp
  · intro X
    refine ⟨∑ p : n, Complex.normSq (X p i), ?_, ?_⟩
    · exact Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
    · simp only [entryFunctional_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      push_cast
      exact Finset.sum_congr rfl fun p _ => by
        rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  · intro d
    simp [Matrix.diagonal_apply_eq]
  · rintro f ⟨hst, hdiag⟩
    have hdiagunit : ∀ k : n, f (Matrix.single k k 1) = if k = i then 1 else 0 := by
      intro k
      rw [← Matrix.diagonal_single k (1 : ℂ), hdiag]
      by_cases h : k = i <;> simp [Pi.single_apply, h]
    have hzero : ∀ q s : n, ¬(q = i ∧ s = i) → f (Matrix.single q s 1) = 0 := by
      intro q s hqs
      by_cases hqsEq : q = s
      · subst hqsEq
        have : q ≠ i := by tauto
        simp [hdiagunit q, this]
      · by_cases hq : q = i
        · have hs : s ≠ i := by tauto
          have hss : f (Matrix.single s s 1) = 0 := by simp [hdiagunit s, hs]
          exact ((offdiag_eq_zero hst (Ne.symm hqsEq) hss).2)
        · have hqq : f (Matrix.single q q 1) = 0 := by simp [hdiagunit q, hq]
          exact ((offdiag_eq_zero hst hqsEq hqq).1)
    ext A
    rw [linearMap_apply_eq_sum f A, entryFunctional_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [hdiagunit i, if_pos rfl, mul_one]
      · intro s _ hs
        rw [hzero i s (by tauto), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro q _ hq
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hzero q s (by tauto), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

end Frontier

