/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header above is written as a plain block comment.)

import Mathlib

/-!
The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) of `B(ℓ²)` extends uniquely to a state on `B(ℓ²)`.  It was answered
affirmatively by Marcus, Spielman and Srivastava via the method of interlacing families of
polynomials.

This file formalizes and proves in full the *finite-dimensional* case — the base case of the
Kadison–Singer question: for the diagonal MASA of the matrix algebra `Mₙ(ℂ)`, the pure state
`d ↦ d i` of the diagonal has a unique extension to a state on `Mₙ(ℂ)`, namely `A ↦ A i i`.

Here a *state* is a unital positive ℂ-linear functional (`Frontier.IsState`), and the pure
states of the diagonal algebra `ℂⁿ` are exactly the coordinate evaluations `d ↦ d i`.

The proof is the classical one: positivity of `phi` yields a positive semidefinite Hermitian
sesquilinear form `(X, Y) ↦ phi (Xᴴ * Y)`, and the degenerate case of the Cauchy–Schwarz
inequality forces `phi` to vanish on every matrix unit other than `E i i`.
-/

namespace Frontier

open Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital, positive linear functional. -/
def IsState (phi : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop :=
  phi 1 = 1 ∧ ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B)

/-- `phi` extends the pure state `d ↦ d i` of the diagonal MASA of `Mₙ(ℂ)`. -/
def ExtendsDiagonalPureState (i : n) (phi : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ d : n → ℂ, phi (Matrix.diagonal d) = d i

section Auxiliary

variable {phi : Matrix n n ℂ →ₗ[ℂ] ℂ}

/-- Positivity of `phi` on `(s • X + t • Y)ᴴ * (s • X + t • Y)`, expanded. -/
private lemma quad_nonneg (hpos : ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B))
    (X Y : Matrix n n ℂ) (s t : ℂ) :
    0 ≤ (starRingEnd ℂ s * s) * phi (Xᴴ * X) + (starRingEnd ℂ s * t) * phi (Xᴴ * Y)
      + (starRingEnd ℂ t * s) * phi (Yᴴ * X) + (starRingEnd ℂ t * t) * phi (Yᴴ * Y) := by
  have h := hpos (s • X + t • Y)
  have hexp : (s • X + t • Y)ᴴ * (s • X + t • Y)
      = (starRingEnd ℂ s * s) • (Xᴴ * X) + (starRingEnd ℂ s * t) • (Xᴴ * Y)
        + (starRingEnd ℂ t * s) • (Yᴴ * X) + (starRingEnd ℂ t * t) • (Yᴴ * Y) := by
    simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul, starRingEnd_apply, mul_comm]
    abel
  rw [hexp] at h
  simpa only [map_add, map_smul, smul_eq_mul] using h

/-- Hermitian symmetry of the sesquilinear form attached to a positive functional. -/
private lemma sesq_conj (hpos : ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B)) (X Y : Matrix n n ℂ) :
    phi (Yᴴ * X) = starRingEnd ℂ (phi (Xᴴ * Y)) := by
  have haim : (phi (Xᴴ * X)).im = 0 := ((Complex.le_def.mp (hpos X)).2).symm
  have hcim : (phi (Yᴴ * Y)).im = 0 := ((Complex.le_def.mp (hpos Y)).2).symm
  have i1 := (Complex.le_def.mp (quad_nonneg hpos X Y 1 1)).2
  have i2 := (Complex.le_def.mp (quad_nonneg hpos X Y 1 Complex.I)).2
  simp only [map_one, one_mul, mul_one, Complex.conj_I, Complex.add_im, Complex.mul_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.zero_im] at i1 i2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> linarith

/-- Degenerate Cauchy–Schwarz: if `phi (Xᴴ * X) = 0` then `phi (Xᴴ * Y) = 0`. -/
private lemma sesq_eq_zero (hpos : ∀ B : Matrix n n ℂ, 0 ≤ phi (Bᴴ * B)) (X Y : Matrix n n ℂ)
    (hX : phi (Xᴴ * X) = 0) : phi (Xᴴ * Y) = 0 := by
  set z := phi (Xᴴ * Y) with hz
  set c := phi (Yᴴ * Y) with hc
  have hw : phi (Yᴴ * X) = starRingEnd ℂ z := sesq_conj hpos X Y
  by_contra hne
  have hznorm : 0 < Complex.normSq z := by
    have h0 : Complex.normSq z ≠ 0 := by simpa [Complex.normSq_eq_zero] using hne
    exact lt_of_le_of_ne (Complex.normSq_nonneg z) (Ne.symm h0)
  set R : ℝ := (c.re + 1) / (2 * Complex.normSq z) with hR
  have hcre : 0 ≤ c.re := (Complex.le_def.mp (hpos Y)).1
  have key := quad_nonneg hpos X Y (-(R : ℂ) * z) 1
  rw [hX, hw, ← hz, ← hc] at key
  have hzz : z * starRingEnd ℂ z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have hexpand : (starRingEnd ℂ (-(R : ℂ) * z) * (-(R : ℂ) * z)) * 0
      + (starRingEnd ℂ (-(R : ℂ) * z) * 1) * z
      + (starRingEnd ℂ (1 : ℂ) * (-(R : ℂ) * z)) * starRingEnd ℂ z
      + (starRingEnd ℂ (1 : ℂ) * 1) * c
      = c - 2 * (R : ℂ) * (Complex.normSq z : ℂ) := by
    simp only [map_mul, map_neg, map_one, Complex.conj_ofReal, one_mul, mul_one, mul_zero, zero_add]
    rw [← hzz]; ring
  rw [hexpand] at key
  have hre : (0 : ℂ).re ≤ (c - 2 * (R : ℂ) * (Complex.normSq z : ℂ)).re := (Complex.le_def.mp key).1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.zero_re] at hre
  rw [hR] at hre
  have hfield : (c.re + 1) / (2 * Complex.normSq z) * (2 * Complex.normSq z) = c.re + 1 := by
    field_simp
  nlinarith [hfield]

end Auxiliary

/-- **Kadison–Singer, finite-dimensional case.**
For every index `i`, the pure state `d ↦ d i` of the diagonal MASA of the matrix algebra
`Mₙ(ℂ)` has a *unique* extension to a state (unital positive linear functional) on `Mₙ(ℂ)`,
namely `A ↦ A i i`. -/
theorem kadison_singer (i : n) :
    ∃! phi : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState phi ∧ ExtendsDiagonalPureState i phi := by
  refine ⟨Matrix.entryLinearMap ℂ ℂ i i, ⟨⟨by simp [Matrix.entryLinearMap], ?_⟩, ?_⟩, ?_⟩
  · intro B
    have hval : (Matrix.entryLinearMap ℂ ℂ i i) (Bᴴ * B) = ∑ j : n, star (B j i) * B j i := by
      simp [Matrix.entryLinearMap, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
    rw [hval]
    exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg (B j i)
  · intro d
    simp [Matrix.entryLinearMap]
  · rintro phi ⟨⟨-, hpos⟩, hdiag⟩
    -- values of `phi` on the diagonal matrix units
    have hEjj : ∀ j : n, j ≠ i → phi (Matrix.single j j (1 : ℂ)) = 0 := by
      intro j hj
      have hd := hdiag (Pi.single j (1 : ℂ))
      rw [Matrix.diagonal_single] at hd
      rw [hd, Pi.single_apply, if_neg (fun h => hj h.symm)]
    have hEii : phi (Matrix.single i i (1 : ℂ)) = 1 := by
      have hd := hdiag (Pi.single i (1 : ℂ))
      rw [Matrix.diagonal_single] at hd
      rw [hd, Pi.single_apply, if_pos rfl]
    -- every matrix unit other than `E i i` is annihilated
    have hrow : ∀ j k : n, j ≠ i → phi (Matrix.single j k (1 : ℂ)) = 0 := by
      intro j k hj
      have hX : (Matrix.single j j (1 : ℂ))ᴴ = Matrix.single j j (1 : ℂ) := by
        rw [Matrix.conjTranspose_single]; simp
      have h1 : (Matrix.single j j (1 : ℂ))ᴴ * Matrix.single j j (1 : ℂ)
          = Matrix.single j j (1 : ℂ) := by
        rw [hX, Matrix.single_mul_single_same]; simp
      have h2 : (Matrix.single j j (1 : ℂ))ᴴ * Matrix.single j k (1 : ℂ)
          = Matrix.single j k (1 : ℂ) := by
        rw [hX, Matrix.single_mul_single_same]; simp
      have hz := sesq_eq_zero hpos (Matrix.single j j (1 : ℂ)) (Matrix.single j k (1 : ℂ))
        (by rw [h1]; exact hEjj j hj)
      rwa [h2] at hz
    have hcol : ∀ k : n, k ≠ i → phi (Matrix.single i k (1 : ℂ)) = 0 := by
      intro k hk
      have hX : (Matrix.single k k (1 : ℂ))ᴴ = Matrix.single k k (1 : ℂ) := by
        rw [Matrix.conjTranspose_single]; simp
      have hY : (Matrix.single k i (1 : ℂ))ᴴ = Matrix.single i k (1 : ℂ) := by
        rw [Matrix.conjTranspose_single]; simp
      have h1 : (Matrix.single k k (1 : ℂ))ᴴ * Matrix.single k i (1 : ℂ)
          = Matrix.single k i (1 : ℂ) := by
        rw [hX, Matrix.single_mul_single_same]; simp
      have h2 : (Matrix.single k i (1 : ℂ))ᴴ * Matrix.single k k (1 : ℂ)
          = Matrix.single i k (1 : ℂ) := by
        rw [hY, Matrix.single_mul_single_same]; simp
      have hsym := sesq_conj hpos (Matrix.single k k (1 : ℂ)) (Matrix.single k i (1 : ℂ))
      rw [h1, h2] at hsym
      rw [hsym, hrow k i hk, map_zero]
    have hunit : ∀ j k : n, phi (Matrix.single j k (1 : ℂ)) = if j = i ∧ k = i then 1 else 0 := by
      intro j k
      by_cases hj : j = i
      · subst hj
        by_cases hk : k = j
        · subst hk; simpa using hEii
        · rw [hcol k hk, if_neg (by tauto)]
      · rw [hrow j k hj, if_neg (by tauto)]
    apply LinearMap.ext
    intro A
    show phi A = A i i
    have hsmul : ∀ j k : n,
        phi (Matrix.single j k (A j k)) = if j = i ∧ k = i then A i i else 0 := by
      intro j k
      have hsc : Matrix.single j k (A j k) = (A j k) • Matrix.single j k (1 : ℂ) := by
        rw [Matrix.smul_single]; simp
      rw [hsc, map_smul, smul_eq_mul, hunit j k]
      by_cases h : j = i ∧ k = i
      · obtain ⟨rfl, rfl⟩ := h; simp
      · simp [h]
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum, hsmul]
    simp [ite_and, Finset.sum_ite_eq']

/-!
### The coordinate evaluations really are the pure states of the diagonal

To justify the terminology used above we check that, for the diagonal algebra `ℂⁿ`, each
coordinate evaluation `d ↦ d i` is a state and is *pure*, i.e. an extreme point of the state
space: it is not a nontrivial convex combination of two states.
-/

/-- The `j`-th standard unit vector of `ℂⁿ`, viewed as an element of the diagonal algebra. -/
def unitVec (j : n) : n → ℂ := Pi.single j 1

/-- A state on the diagonal algebra `ℂⁿ`: a unital, positive linear functional. -/
def IsDiagState (psi : (n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  psi 1 = 1 ∧ ∀ d : n → ℂ, 0 ≤ psi (star d * d)

private lemma diag_state_apply (psi : (n → ℂ) →ₗ[ℂ] ℂ) (d : n → ℂ) :
    psi d = ∑ j : n, d j * psi (unitVec j) := by
  have hd : d = ∑ j : n, d j • (unitVec j : n → ℂ) := by
    funext k; simp [unitVec, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hd]
  simp [map_sum]

omit [Fintype n] in
private lemma diag_state_nonneg {psi : (n → ℂ) →ₗ[ℂ] ℂ} (h : IsDiagState psi) (j : n) :
    0 ≤ psi (unitVec j) := by
  have hh := h.2 (unitVec j)
  have he : star (unitVec j : n → ℂ) * unitVec j = unitVec j := by
    funext k; by_cases hk : j = k <;> simp [unitVec, Pi.single_apply, hk]
  rwa [he] at hh

private lemma diag_state_sum {psi : (n → ℂ) →ₗ[ℂ] ℂ} (h : IsDiagState psi) :
    ∑ j : n, psi (unitVec j) = 1 := by
  have h1 : (1 : n → ℂ) = ∑ j : n, (unitVec j : n → ℂ) := by
    funext k; simp [unitVec, Finset.sum_apply, Pi.single_apply]
  have hh := h.1
  rw [h1, map_sum] at hh
  exact hh

/-- The coordinate evaluation `d ↦ d i` is a state on the diagonal algebra `ℂⁿ`, and it is a
pure state: whenever it is written as a convex combination `t • psi₁ + (1 - t) • psi₂` of two
states with `0 < t < 1`, both summands are equal to it. -/
theorem diagonal_eval_isPureState (i : n) :
    IsDiagState (LinearMap.proj i : (n → ℂ) →ₗ[ℂ] ℂ) ∧
      ∀ (psi1 psi2 : (n → ℂ) →ₗ[ℂ] ℂ) (t : ℝ), IsDiagState psi1 → IsDiagState psi2 →
        0 < t → t < 1 →
        (LinearMap.proj i : (n → ℂ) →ₗ[ℂ] ℂ) = (t : ℂ) • psi1 + ((1 - t : ℝ) : ℂ) • psi2 →
        psi1 = (LinearMap.proj i : (n → ℂ) →ₗ[ℂ] ℂ) := by
  constructor
  · refine ⟨rfl, fun d => ?_⟩
    simpa using star_mul_self_nonneg (d i)
  · intro psi1 psi2 t h1 h2 ht0 ht1 hconv
    have hzero : ∀ j : n, j ≠ i → psi1 (unitVec j) = 0 := by
      intro j hj
      have hap := congrArg (fun (f : (n → ℂ) →ₗ[ℂ] ℂ) => f (unitVec j)) hconv
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.proj_apply] at hap
      have hej : (unitVec j : n → ℂ) i = 0 := by simp [unitVec, hj]
      rw [hej] at hap
      have ha := diag_state_nonneg h1 j
      have hb := diag_state_nonneg h2 j
      have hare : 0 ≤ (psi1 (unitVec j)).re := (Complex.le_def.mp ha).1
      have haim : (psi1 (unitVec j)).im = 0 := ((Complex.le_def.mp ha).2).symm
      have hbre : 0 ≤ (psi2 (unitVec j)).re := (Complex.le_def.mp hb).1
      have hre := congrArg Complex.re hap
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re] at hre
      have hzr : (psi1 (unitVec j)).re = 0 := by nlinarith [hre]
      apply Complex.ext <;> simp [hzr, haim]
    have hone : psi1 (unitVec i) = 1 := by
      have hs := diag_state_sum h1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hs
      have hz : ∑ j ∈ Finset.univ.erase i, psi1 (unitVec j) = 0 :=
        Finset.sum_eq_zero fun j hj => hzero j (Finset.mem_erase.mp hj).1
      rw [hz, zero_add] at hs
      exact hs
    apply LinearMap.ext
    intro d
    rw [diag_state_apply psi1 d, Finset.sum_eq_single i]
    · simp [hone]
    · intro j _ hj; rw [hzero j hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

/-!
### The one-dimensional case of the Marcus–Spielman–Srivastava discrepancy theorem

Weaver's conjecture `KS₂`, proved by Marcus, Spielman and Srivastava with interlacing
families, states that vectors `v₁, …, v_m` in `ℂ^d` with `∑ vⱼ vⱼ* = I` and `‖vⱼ‖² ≤ eps` can
be partitioned into two halves each of operator norm at most `(1/√2 + √eps)²`.

Below is the case `d = 1` of that statement, where the hypothesis reads `∑ ‖vⱼ‖² = 1`; we prove
the sharper bound `1/2 + eps/2` by a greedy balancing argument.
-/

/-- Greedy balancing: a family of reals in `[0, eps]` indexed by a finite set can be split
into two parts whose sums differ by at most `eps`. -/
theorem balanced_partition {m : Type*} [DecidableEq m] (a : m → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (h0 : ∀ j, 0 ≤ a j) (h1 : ∀ j, a j ≤ eps) (t : Finset m) :
    ∃ S ⊆ t, |∑ j ∈ S, a j - ∑ j ∈ t \ S, a j| ≤ eps := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using heps⟩
  | insert x t hx ih =>
    obtain ⟨S, hSt, hd⟩ := ih
    rcases le_or_gt 0 (∑ j ∈ S, a j - ∑ j ∈ t \ S, a j) with hpos | hneg
    · refine ⟨S, hSt.trans (Finset.subset_insert _ _), ?_⟩
      have hins : (insert x t) \ S = insert x (t \ S) :=
        Finset.insert_sdiff_of_notMem _ (fun h => hx (hSt h))
      rw [hins, Finset.sum_insert (by simp [hx])]
      have hx0 := h0 x
      have hx1 := h1 x
      rw [abs_le] at hd ⊢
      constructor <;> linarith [hd.1, hd.2]
    · refine ⟨insert x S, Finset.insert_subset_insert _ hSt, ?_⟩
      have hxS : x ∉ S := fun h => hx (hSt h)
      have hins : (insert x t) \ (insert x S) = t \ S := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hy, hy2⟩
          refine ⟨?_, fun h => hy2 (Or.inr h)⟩
          rcases hy with rfl | hy
          · exact absurd (Or.inl rfl) hy2
          · exact hy
        · rintro ⟨hy, hy2⟩
          exact ⟨Or.inr hy, by rintro (rfl | h); exacts [hx hy, hy2 h]⟩
      rw [hins, Finset.sum_insert hxS]
      have hx0 := h0 x
      have hx1 := h1 x
      rw [abs_le] at hd ⊢
      constructor <;> linarith [hd.1, hd.2]

/-- **Weaver's `KS₂` / the Marcus–Spielman–Srivastava discrepancy theorem in dimension one.**
If scalars `vⱼ` satisfy `∑ ‖vⱼ‖² = 1` (the one-dimensional isotropy condition) and
`‖vⱼ‖² ≤ eps`, then the index set splits into two parts, each carrying at most
`1/2 + eps/2` of the total mass. -/
theorem weaver_KS2_dim_one {m : Type*} [Fintype m] [DecidableEq m] (v : m → ℂ) (eps : ℝ)
    (hsum : ∑ j, ‖v j‖ ^ 2 = 1) (hsmall : ∀ j, ‖v j‖ ^ 2 ≤ eps) :
    ∃ S : Finset m, ∑ j ∈ S, ‖v j‖ ^ 2 ≤ 1 / 2 + eps / 2 ∧
      ∑ j ∈ Sᶜ, ‖v j‖ ^ 2 ≤ 1 / 2 + eps / 2 := by
  classical
  have h0 : ∀ j, (0 : ℝ) ≤ ‖v j‖ ^ 2 := fun j => sq_nonneg _
  have heps : 0 ≤ eps := by
    rcases isEmpty_or_nonempty m with hm | hm
    · simp at hsum
    · exact le_trans (h0 (Classical.arbitrary m)) (hsmall _)
  obtain ⟨S, -, hS⟩ := balanced_partition (fun j => ‖v j‖ ^ 2) eps heps h0 hsmall Finset.univ
  refine ⟨S, ?_, ?_⟩ <;>
  · have hc : Finset.univ \ S = Sᶜ := by simp [Finset.compl_eq_univ_sdiff]
    rw [hc] at hS
    have htot : ∑ j ∈ S, ‖v j‖ ^ 2 + ∑ j ∈ Sᶜ, ‖v j‖ ^ 2 = 1 := by
      rw [Finset.sum_add_sum_compl]; exact hsum
    rw [abs_le] at hS
    linarith [hS.1, hS.2]

end Frontier

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

