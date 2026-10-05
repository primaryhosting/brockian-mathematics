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

private lemma sum_map_ite_eq_count {a c : ℝ} (s : Multiset ℝ) :
    (s.map (fun x => if x = a then c else 0)).sum = c * (s.count a : ℝ) := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons x s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      rcases eq_or_ne x a with rfl | hx
      · rw [if_pos rfl, Multiset.count_cons_self]
        push_cast
        ring
      · rw [if_neg hx, Multiset.count_cons_of_ne (Ne.symm hx), zero_add]

/-- Two finite multisets of strictly positive reals with the same power sums are equal. -/
theorem multiset_eq_of_powerSums {s t : Multiset ℝ}
    (hs : ∀ x ∈ s, 0 < x) (ht : ∀ x ∈ t, 0 < x)
    (h : ∀ p : ℕ, (s.map (fun x => x ^ (p + 1))).sum = (t.map (fun x => x ^ (p + 1))).sum) :
    s = t := by
  classical
  -- The key step: the two multisets give the same sum for any function of the form
  -- `x ↦ x ^ (m+1) * ∏ v ∈ F, (x - v)`.
  have key : ∀ (F : Finset ℝ) (m : ℕ),
      (s.map (fun x => x ^ (m + 1) * ∏ v ∈ F, (x - v))).sum
        = (t.map (fun x => x ^ (m + 1) * ∏ v ∈ F, (x - v))).sum := by
    intro F
    induction F using Finset.induction with
    | empty => intro m; simpa using h m
    | insert w F' hw ih =>
        intro m
        have expand : ∀ x : ℝ, x ^ (m + 1) * ∏ v ∈ insert w F', (x - v)
            = x ^ (m + 1 + 1) * (∏ v ∈ F', (x - v))
              + (-w) * (x ^ (m + 1) * ∏ v ∈ F', (x - v)) := by
          intro x
          rw [Finset.prod_insert hw]
          ring
        simp only [expand]
        rw [Multiset.sum_map_add, Multiset.sum_map_add,
          Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, ih (m + 1), ih m]
  refine Multiset.ext.2 fun a => ?_
  rcases le_or_gt a 0 with ha | ha
  · rw [Multiset.count_eq_zero_of_notMem (fun hmem => absurd (hs a hmem) (not_lt.2 ha)),
      Multiset.count_eq_zero_of_notMem (fun hmem => absurd (ht a hmem) (not_lt.2 ha))]
  · set V : Finset ℝ := s.toFinset ∪ t.toFinset with hV
    set F : Finset ℝ := V.erase a with hF
    set c : ℝ := a * ∏ v ∈ F, (a - v) with hc
    have hcne : c ≠ 0 := by
      refine mul_ne_zero (ne_of_gt ha) (Finset.prod_ne_zero_iff.2 fun v hv => ?_)
      have hva : v ≠ a := Finset.ne_of_mem_erase hv
      exact sub_ne_zero.2 (Ne.symm hva)
    have hval : ∀ (m : Multiset ℝ), (∀ x ∈ m, x ∈ V) →
        (m.map (fun x => x ^ (0 + 1) * ∏ v ∈ F, (x - v))).sum = c * (m.count a : ℝ) := by
      intro m hm
      rw [← sum_map_ite_eq_count (a := a) (c := c) m]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun x hx => ?_)
      rcases eq_or_ne x a with rfl | hxa
      · rw [if_pos rfl, hc]
        ring
      · have hxF : x ∈ F := Finset.mem_erase.2 ⟨hxa, hm x hx⟩
        rw [if_neg hxa, Finset.prod_eq_zero hxF (by ring)]
        ring
    have h1 : (∀ x ∈ s, x ∈ V) := fun x hx =>
      Finset.mem_union_left _ (Multiset.mem_toFinset.2 hx)
    have h2 : (∀ x ∈ t, x ∈ V) := fun x hx =>
      Finset.mem_union_right _ (Multiset.mem_toFinset.2 hx)
    have hkey := key F 0
    rw [hval s h1, hval t h2] at hkey
    exact_mod_cast mul_left_cancel₀ hcne hkey

/-! ### Traces of powers of the reduced density matrix -/

section Trace

variable [Fintype A] [Fintype B] [DecidableEq A]
variable {M : Matrix A B ℂ} {r : ℕ} {lam : Fin r → ℝ} {e : Fin r → A → ℂ} {f : Fin r → B → ℂ}

/-- The matrix whose columns are the left Schmidt vectors. -/
private def leftMat (e : Fin r → A → ℂ) : Matrix A (Fin r) ℂ := Matrix.of fun i k => e k i

omit [DecidableEq A] in
private lemma leftMat_conjTranspose_mul (h : IsSchmidtDecomposition M r lam e f) :
    (leftMat e)ᴴ * (leftMat e) = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, leftMat, Matrix.of_apply,
    Matrix.one_apply, RCLike.star_def]
  exact h.left_orthonormal k l

omit [DecidableEq A] in
private lemma reducedDensity_eq (h : IsSchmidtDecomposition M r lam e f) :
    M * Mᴴ = (leftMat e) * Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2)) * (leftMat e)ᴴ := by
  classical
  ext i i'
  have hR : ∀ k l : Fin r, ∑ j, f k j * conj (f l j) = if l = k then (1 : ℂ) else 0 := by
    intro k l
    rw [← h.right_orthonormal l k]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hRHS : ((leftMat e) * Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2)) * (leftMat e)ᴴ) i i'
      = ∑ k, e k i * ((lam k : ℂ) ^ 2 * conj (e k i')) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diagonal_mul]
    simp [leftMat]
  have hLHS : (M * Mᴴ) i i' = ∑ k, e k i * ((lam k : ℂ) ^ 2 * conj (e k i')) := by
    rw [Matrix.mul_apply]
    have hL : ∀ j : B, M i j * (Mᴴ) j i'
        = ∑ k, ∑ l, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
            * (f k j * conj (f l j)) := by
      intro j
      rw [Matrix.conjTranspose_apply, h.sum_eq i j, h.sum_eq i' j, RCLike.star_def, map_sum,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [map_mul, Complex.conj_ofReal]
      ring
    simp only [hL]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    have hin : ∀ l : Fin r, ∑ j, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
          * (f k j * conj (f l j))
        = ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
            * (if l = k then (1 : ℂ) else 0) := by
      intro l
      rw [← hR k l, Finset.mul_sum]
    simp only [hin]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
      ring
    · intro l _ hlk
      rw [if_neg hlk, mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ k) hc
  rw [hLHS, hRHS]

private lemma pow_reducedDensity (h : IsSchmidtDecomposition M r lam e f) (p : ℕ) :
    (M * Mᴴ) ^ (p + 1)
      = (leftMat e) * (Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2))) ^ (p + 1) * (leftMat e)ᴴ := by
  induction p with
  | zero => simpa using reducedDensity_eq h
  | succ n ih =>
      rw [pow_succ, ih, reducedDensity_eq h]
      rw [pow_succ (Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2))) (n + 1)]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((leftMat e)ᴴ) (leftMat e), leftMat_conjTranspose_mul h,
        Matrix.one_mul]

/-- The trace of the `(p+1)`-st power of the reduced density matrix `M Mᴴ` is the
`(p+1)`-st power sum of the squared Schmidt coefficients. -/
theorem trace_pow_eq (h : IsSchmidtDecomposition M r lam e f) (p : ℕ) :
    ((M * Mᴴ) ^ (p + 1)).trace = ((∑ k, (lam k) ^ (2 * (p + 1)) : ℝ) : ℂ) := by
  rw [pow_reducedDensity h p,
    Matrix.trace_mul_comm ((leftMat e) * (Matrix.diagonal (fun k => ((lam k : ℂ) ^ 2))) ^ (p + 1))
      ((leftMat e)ᴴ), ← Matrix.mul_assoc, leftMat_conjTranspose_mul h, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.pow_apply]
  rw [← pow_mul]

end Trace

/-! ### Existence -/

/-- Spectral theorem, packaged as an orthonormal eigenbasis written out in coordinates. -/
private lemma exists_orthonormal_eigenbasis [Fintype A] [DecidableEq A] {R : Matrix A A ℂ}
    (hR : R.IsHermitian) :
    ∃ (mu : A → ℝ) (u : A → A → ℂ),
      (∀ k l, ∑ i, conj (u k i) * u l i = if k = l then (1 : ℂ) else 0) ∧
      (∀ i i', ∑ k, u k i * conj (u k i') = if i = i' then (1 : ℂ) else 0) ∧
      (∀ k, R *ᵥ (u k) = (mu k : ℂ) • (u k)) := by
  classical
  refine ⟨hR.eigenvalues, fun k i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k, ?_, ?_, ?_⟩
  · intro k l
    have hs := (hR.eigenvectorUnitary.2 : (hR.eigenvectorUnitary : Matrix A A ℂ) ∈ unitary _).1
    have := congrFun (congrFun hs k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, RCLike.star_def] using this
  · intro i i'
    have hs := (hR.eigenvectorUnitary.2 : (hR.eigenvectorUnitary : Matrix A A ℂ) ∈ unitary _).2
    have := congrFun (congrFun hs i) i'
    simpa [Matrix.mul_apply, Matrix.one_apply, RCLike.star_def] using this
  · intro k
    have h1 := hR.mulVec_eigenvectorBasis k
    show R *ᵥ (fun i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k)
        = ((hR.eigenvalues k : ℝ) : ℂ) • (fun i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k)
    have h2 : (fun i => (hR.eigenvectorUnitary : Matrix A A ℂ) i k)
        = (hR.eigenvectorBasis k).ofLp := rfl
    rw [h2, h1]
    funext i
    simp [Complex.real_smul]

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
theorem schmidt_decomposition [Fintype A] [Fintype B] [DecidableEq A] (M : Matrix A B ℂ)
    (hM : ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1) :
    (∃ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ),
        IsSchmidtDecomposition M r lam e f ∧ ∑ k, lam k ^ 2 = 1) ∧
      (∀ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ)
         (r' : ℕ) (lam' : Fin r' → ℝ) (e' : Fin r' → A → ℂ) (f' : Fin r' → B → ℂ),
          IsSchmidtDecomposition M r lam e f → IsSchmidtDecomposition M r' lam' e' f' →
            r = r' ∧
              (Finset.univ.val.map lam : Multiset ℝ)
                = (Finset.univ.val.map lam' : Multiset ℝ)) := by
  classical
  have htrace : (M * Mᴴ).trace = ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj']
  have hnorm : ∀ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → A → ℂ) (f : Fin r → B → ℂ),
      IsSchmidtDecomposition M r lam e f → ∑ k, lam k ^ 2 = 1 := by
    intro r lam e f h
    have ht := trace_pow_eq h 0
    rw [pow_one, htrace, hM] at ht
    have h3 : (1 : ℝ) = ∑ k, lam k ^ (2 * (0 + 1)) := by exact_mod_cast ht
    simpa using h3.symm
  constructor
  · obtain ⟨r, lam, e, f, h⟩ := exists_isSchmidtDecomposition (B := B) M
    exact ⟨r, lam, e, f, h, hnorm r lam e f h⟩
  · intro r lam e f r' lam' e' f' h h'
    have hps : ∀ p : ℕ, ∑ k, (lam k ^ 2) ^ (p + 1) = ∑ k, (lam' k ^ 2) ^ (p + 1) := by
      intro p
      have e1 := trace_pow_eq h p
      have e2 := trace_pow_eq h' p
      rw [e1] at e2
      have e3 : (∑ k, lam k ^ (2 * (p + 1)) : ℝ) = ∑ k, lam' k ^ (2 * (p + 1)) := by
        exact_mod_cast e2
      simpa [← pow_mul] using e3
    set s : Multiset ℝ := (Finset.univ.val : Multiset (Fin r)).map (fun k => lam k ^ 2) with hsdef
    set t : Multiset ℝ := (Finset.univ.val : Multiset (Fin r')).map (fun k => lam' k ^ 2) with htdef
    have hspos : ∀ x ∈ s, 0 < x := by
      intro x hx
      rw [hsdef, Multiset.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      exact pow_pos (h.coeff_pos k) 2
    have htpos : ∀ x ∈ t, 0 < x := by
      intro x hx
      rw [htdef, Multiset.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      exact pow_pos (h'.coeff_pos k) 2
    have hpow : ∀ p : ℕ,
        (s.map (fun x => x ^ (p + 1))).sum = (t.map (fun x => x ^ (p + 1))).sum := by
      intro p
      rw [hsdef, htdef, Multiset.map_map, Multiset.map_map]
      exact hps p
    have hst : s = t := multiset_eq_of_powerSums hspos htpos hpow
    have hmap : (Finset.univ.val.map lam : Multiset ℝ)
        = (Finset.univ.val.map lam' : Multiset ℝ) := by
      have hl : (Finset.univ.val.map lam : Multiset ℝ) = s.map Real.sqrt := by
        rw [hsdef, Multiset.map_map]
        refine Multiset.map_congr rfl fun k _ => ?_
        simp only [Function.comp_apply]
        exact (Real.sqrt_sq (le_of_lt (h.coeff_pos k))).symm
      have hl' : (Finset.univ.val.map lam' : Multiset ℝ) = t.map Real.sqrt := by
        rw [htdef, Multiset.map_map]
        refine Multiset.map_congr rfl fun k _ => ?_
        simp only [Function.comp_apply]
        exact (Real.sqrt_sq (le_of_lt (h'.coeff_pos k))).symm
      rw [hl, hl', hst]
    refine ⟨?_, hmap⟩
    have hcard := congrArg Multiset.card hmap
    simpa using hcard

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

