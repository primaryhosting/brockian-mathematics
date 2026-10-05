/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix ComplexConjugate

namespace QI

variable {A B : Type*}

/-- `IsSchmidtDecomposition M r lam e f` says that the bipartite pure state whose amplitude
matrix is `M` (so that the state is `∑ i j, M i j • |i⟩ ⊗ |j⟩`) is written as

`M i j = ∑ k, (lam k) * e k i * f k j`

where the `lam k` are strictly positive real *Schmidt coefficients* and `e`, `f` are
orthonormal families in the two tensor factors. -/
structure IsSchmidtDecomposition [Fintype A] [Fintype B] (M : Matrix A B ℂ) (r : ℕ)
    (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ) : Prop where
  /-- Schmidt coefficients are strictly positive. -/
  coeff_pos : ∀ k, 0 < lam k
  /-- The left Schmidt vectors are orthonormal. -/
  left_orthonormal : ∀ k l, ∑ i, conj (e k i) * e l i = if k = l then 1 else 0
  /-- The right Schmidt vectors are orthonormal. -/
  right_orthonormal : ∀ k l, ∑ j, conj (f k j) * f l j = if k = l then 1 else 0
  /-- The state is the corresponding sum of product states. -/
  sum_eq : ∀ i j, M i j = ∑ k, (lam k : ℂ) * e k i * f k j

/-! ### A multiset of positive reals is determined by its power sums -/


theorem exists_isSchmidtDecomposition [Fintype A] [Fintype B] [DecidableEq A] (M : Matrix A B ℂ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ),
      IsSchmidtDecomposition M r lam e f := by
  classical
  have hher : (M * Mᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  obtain ⟨mu, u, hon, hcomp, heig⟩ := exists_orthonormal_eigenbasis hher
  set w : A → B → ℂ := fun k j => ∑ a, conj (u k a) * M a j with hwdef
  have hww : ∀ k l, ∑ j, conj (w k j) * w l j
      = (mu k : ℂ) * (if l = k then (1 : ℂ) else 0) := by
    intro k l
    have step1 : ∀ j : B, conj (w k j) * w l j
        = ∑ a, ∑ b, (u k a * conj (u l b)) * (conj (M a j) * M b j) := by
      intro j
      simp only [hwdef, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [step1]
    rw [Finset.sum_comm]
    have step2 : ∀ a : A, ∑ j, ∑ b, (u k a * conj (u l b)) * (conj (M a j) * M b j)
        = ∑ b, (u k a * conj (u l b)) * (M * Mᴴ) b a := by
      intro a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def]
      ring
    simp only [step2]
    rw [Finset.sum_comm]
    have step3 : ∀ b : A, ∑ a, (u k a * conj (u l b)) * (M * Mᴴ) b a
        = conj (u l b) * ((mu k : ℂ) * u k b) := by
      intro b
      have hswap : ∑ a, (u k a * conj (u l b)) * (M * Mᴴ) b a
          = conj (u l b) * ∑ a, (M * Mᴴ) b a * u k a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hswap]
      have hmv : ∑ a, (M * Mᴴ) b a * u k a = ((mu k : ℂ) • (u k)) b := by
        rw [← heig k]
        simp [Matrix.mulVec, dotProduct]
      rw [hmv]
      simp
    simp only [step3]
    have hfin : ∑ b, conj (u l b) * ((mu k : ℂ) * u k b)
        = (mu k : ℂ) * ∑ b, conj (u l b) * u k b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hfin, hon l k]
  have hnormw : ∀ k, mu k = ∑ j, ‖w k j‖ ^ 2 := by
    intro k
    have hk := hww k k
    rw [if_pos rfl, mul_one] at hk
    have h2 : ∑ j, conj (w k j) * w k j = ((∑ j, ‖w k j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm, Complex.mul_conj']
    rw [h2] at hk
    exact_mod_cast hk.symm
  have hmunonneg : ∀ k, 0 ≤ mu k := by
    intro k
    rw [hnormw k]
    exact Finset.sum_nonneg fun j _ => by positivity
  have hwzero : ∀ k, mu k = 0 → ∀ j, w k j = 0 := by
    intro k hk j
    have hz := (hnormw k).symm
    rw [hk] at hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 hz j
      (Finset.mem_univ j)
    simpa using hall
  -- Select the nonzero eigenvalues.
  set S : Finset A := Finset.univ.filter (fun k => mu k ≠ 0) with hS
  set r : ℕ := S.card with hr
  set idx : Fin r → A := fun k => ((S.equivFin.symm k : S) : A) with hidx
  have hidx_mem : ∀ k, idx k ∈ S := fun k => (S.equivFin.symm k).2
  have hidx_inj : Function.Injective idx := by
    intro k l hkl
    exact S.equivFin.symm.injective (Subtype.ext hkl)
  have hmupos : ∀ k, 0 < mu (idx k) := by
    intro k
    have hm := hidx_mem k
    rw [hS, Finset.mem_filter] at hm
    exact lt_of_le_of_ne (hmunonneg _) (Ne.symm hm.2)
  set lam : Fin r → ℝ := fun k => Real.sqrt (mu (idx k)) with hlam
  have hlampos : ∀ k, 0 < lam k := fun k => Real.sqrt_pos.2 (hmupos k)
  have hlamsq : ∀ k, (lam k) ^ 2 = mu (idx k) := fun k =>
    Real.sq_sqrt (le_of_lt (hmupos k))
  refine ⟨r, lam, fun k => u (idx k), fun k j => (lam k : ℂ)⁻¹ * w (idx k) j,
    hlampos, ?_, ?_, ?_⟩
  · intro k l
    rw [hon (idx k) (idx l)]
    by_cases hkl : k = l
    · rw [hkl, if_pos rfl, if_pos rfl]
    · rw [if_neg hkl, if_neg (fun hc => hkl (hidx_inj hc))]
  · intro k l
    have hpull : ∑ j, conj ((lam k : ℂ)⁻¹ * w (idx k) j) * ((lam l : ℂ)⁻¹ * w (idx l) j)
        = ((lam k : ℂ)⁻¹ * (lam l : ℂ)⁻¹) * ∑ j, conj (w (idx k) j) * w (idx l) j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    rw [hpull, hww (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, mul_one]
      have h2 : ((lam k : ℂ)) ≠ 0 := by
        simpa using ne_of_gt (hlampos k)
      have h3 : ((mu (idx k) : ℂ)) = (lam k : ℂ) ^ 2 := by
        rw [← hlamsq k]
        push_cast
        ring
      rw [h3]
      field_simp
    · rw [if_neg (fun hc => hkl (hidx_inj hc).symm), if_neg hkl]
      ring
  · intro i j
    have hsum : ∀ k : Fin r, (lam k : ℂ) * u (idx k) i * ((lam k : ℂ)⁻¹ * w (idx k) j)
        = u (idx k) i * w (idx k) j := by
      intro k
      have h2 : ((lam k : ℂ)) ≠ 0 := by
        simpa using ne_of_gt (hlampos k)
      field_simp
    simp only [hsum]
    have reindex : ∀ g : A → ℂ, ∑ k : Fin r, g (idx k) = ∑ a ∈ S, g a := by
      intro g
      rw [← Finset.sum_coe_sort S g]
      exact Fintype.sum_equiv (S.equivFin.symm) _ _ (fun k => rfl)
    rw [reindex (fun a => u a i * w a j)]
    have hext : ∑ a ∈ S, u a i * w a j = ∑ a : A, u a i * w a j := by
      refine Finset.sum_subset (Finset.subset_univ S) ?_
      intro a _ hnot
      rw [hS, Finset.mem_filter] at hnot
      have hz : mu a = 0 := by
        by_contra hcon
        exact hnot ⟨Finset.mem_univ a, hcon⟩
      rw [hwzero a hz j, mul_zero]
    rw [hext]
    have hexp : ∀ a : A, u a i * w a j = ∑ b, (u a i * conj (u a b)) * M b j := by
      intro a
      rw [hwdef]
      simp only
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp only [hexp]
    rw [Finset.sum_comm]
    have hcol : ∀ b : A, ∑ a, (u a i * conj (u a b)) * M b j
        = (if i = b then (1 : ℂ) else 0) * M b j := by
      intro b
      rw [← Finset.sum_mul, hcomp i b]
    simp only [hcol]
    simp

/-! ### The main theorem -/

/-- **Schmidt decomposition.**  Let `M` be the amplitude matrix of a bipartite pure state on
`ℂ^A ⊗ ℂ^B`, normalised so that `∑ i j, ‖M i j‖ ^ 2 = 1`.

*Existence*: there is a Schmidt decomposition `M i j = ∑ k, lam k * e k i * f k j` with
strictly positive Schmidt coefficients `lam` and orthonormal families `e`, `f`, and the
coefficients satisfy `∑ k, lam k ^ 2 = 1`.

*Uniqueness*: any two Schmidt decompositions of `M` have the same Schmidt rank and the same
multiset of Schmidt coefficients. -/
