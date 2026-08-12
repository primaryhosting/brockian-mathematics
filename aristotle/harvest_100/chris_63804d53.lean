import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/
theorem multiset_eq_of_powerSum_eq {A B : Multiset ℝ}
    (hA : ∀ x ∈ A, 0 < x) (hB : ∀ x ∈ B, 0 < x)
    (h : ∀ k : ℕ, 1 ≤ k → (A.map (· ^ k)).sum = (B.map (· ^ k)).sum) : A = B := by
  classical
  refine Multiset.ext.mpr fun c => ?_
  set S : Finset ℝ := A.toFinset ∪ B.toFinset with hS
  set d : ℝ → ℝ := fun x => (A.count x : ℝ) - (B.count x : ℝ) with hd
  have hApos : ∀ x ∈ S, (0:ℝ) < x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA x (Multiset.mem_toFinset.mp hx)
    · exact hB x (Multiset.mem_toFinset.mp hx)
  have key : ∀ k : ℕ, 1 ≤ k → ∑ x ∈ S, d x * x ^ k = 0 := by
    intro k hk
    have hAk : (A.map (· ^ k)).sum = ∑ x ∈ S, (A.count x : ℝ) * x ^ k := by
      calc (A.map (· ^ k)).sum = ∑ x ∈ A.toFinset, A.count x • x ^ k :=
            Finset.sum_multiset_map_count A _
        _ = ∑ x ∈ A.toFinset, (A.count x : ℝ) * x ^ k := by simp [nsmul_eq_mul]
        _ = ∑ x ∈ S, (A.count x : ℝ) * x ^ k := by
            refine Finset.sum_subset Finset.subset_union_left ?_
            intro x _ hx
            simp [Multiset.count_eq_zero.mpr (fun hm => hx (Multiset.mem_toFinset.mpr hm))]
    have hBk : (B.map (· ^ k)).sum = ∑ x ∈ S, (B.count x : ℝ) * x ^ k := by
      calc (B.map (· ^ k)).sum = ∑ x ∈ B.toFinset, B.count x • x ^ k :=
            Finset.sum_multiset_map_count B _
        _ = ∑ x ∈ B.toFinset, (B.count x : ℝ) * x ^ k := by simp [nsmul_eq_mul]
        _ = ∑ x ∈ S, (B.count x : ℝ) * x ^ k := by
            refine Finset.sum_subset Finset.subset_union_right ?_
            intro x _ hx
            simp [Multiset.count_eq_zero.mpr (fun hm => hx (Multiset.mem_toFinset.mpr hm))]
    have hk' := h k hk
    rw [hAk, hBk] at hk'
    have hzero : ∑ x ∈ S, ((A.count x : ℝ) * x ^ k - (B.count x : ℝ) * x ^ k) = 0 := by
      rw [Finset.sum_sub_distrib, hk', sub_self]
    rw [← hzero]
    exact Finset.sum_congr rfl fun x _ => by simp [hd]; ring
  have main : ∀ c ∈ S, d c = 0 := by
    intro c hc
    have hc0 : (0:ℝ) < c := hApos c hc
    set p : ℝ[X] := X * ∏ y ∈ S.erase c, (C (c - y)⁻¹ * (X - C y)) with hp
    have hpc : p.eval c = c := by
      rw [hp]
      simp only [eval_mul, eval_X, eval_prod, eval_sub, eval_C]
      rw [Finset.prod_congr rfl (fun y hy => ?_), Finset.prod_const_one, mul_one]
      have : c - y ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hy))
      field_simp
    have hpy : ∀ y ∈ S, y ≠ c → p.eval y = 0 := by
      intro y hy hyc
      rw [hp]
      simp only [eval_mul, eval_prod, eval_sub, eval_C, eval_X]
      have hmem : y ∈ S.erase c := Finset.mem_erase.mpr ⟨hyc, hy⟩
      rw [Finset.prod_eq_zero hmem (by simp)]
      ring
    have hp0 : p.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hp]
      simp
    have hsum : ∑ x ∈ S, d x * p.eval x = 0 := by
      have hrw : ∀ x ∈ S, d x * p.eval x
          = ∑ i ∈ Finset.range (p.natDegree + 1), (d x * p.coeff i) * x ^ i := by
        intro x _
        rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl hrw, Finset.sum_comm]
      refine Finset.sum_eq_zero fun i hi => ?_
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0; simp [hp0]
      · calc ∑ x ∈ S, (d x * p.coeff i) * x ^ i = p.coeff i * ∑ x ∈ S, d x * x ^ i := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
          _ = 0 := by rw [key i hi0, mul_zero]
    have hsingle : ∑ x ∈ S, d x * p.eval x = d c * c := by
      rw [Finset.sum_eq_single c]
      · rw [hpc]
      · intro x hx hxc
        rw [hpy x hx hxc, mul_zero]
      · intro hcS; exact absurd hc hcS
    rw [hsingle] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right (ne_of_gt hc0)
  by_cases hcS : c ∈ S
  · have hdc := main c hcS
    simp only [hd, sub_eq_zero] at hdc
    exact_mod_cast hdc
  · have h1 : A.count c = 0 := Multiset.count_eq_zero.mpr fun hm =>
      hcS (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hm))
    have h2 : B.count c = 0 := Multiset.count_eq_zero.mpr fun hm =>
      hcS (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hm))
    rw [h1, h2]

/-! ### Outer products -/

/-- The rank-one matrix `x yᴴ`. -/
noncomputable def outer {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun j a => x j * (starRingEnd ℂ) (y a)

lemma outer_apply {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) (j a : Fin m) :
    outer x y j a = x j * (starRingEnd ℂ) (y a) := rfl

lemma outer_mul_outer {m : ℕ} (x y z w : EuclideanSpace ℂ (Fin m)) :
    outer x y * outer z w = (inner ℂ y z : ℂ) • outer x w := by
  ext j a
  simp [outer, Matrix.mul_apply, PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum,
    mul_comm, mul_left_comm]

lemma trace_outer {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    Matrix.trace (outer x y) = (inner ℂ y x : ℂ) := by
  simp [outer, Matrix.trace, Matrix.diag, PiLp.inner_apply, RCLike.inner_apply]

/-- Coordinate form of orthonormality. -/
lemma sum_conj_of_orthonormal {N r : ℕ} {v : Fin r → EuclideanSpace ℂ (Fin N)}
    (hv : Orthonormal ℂ v) (i l : Fin r) :
    ∑ k, v i k * (starRingEnd ℂ) (v l k) = if i = l then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hv) l i
  rw [PiLp.inner_apply] at h
  simp only [RCLike.inner_apply] at h
  simpa [mul_comm, eq_comm] using h

/-! ### The Schmidt decomposition predicate -/

/-- `IsSchmidtDecomposition psi s u v` says that the bipartite state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, presented via its amplitudes indexed by pairs) is written as
`∑ i, s i • (u i ⊗ v i)` with strictly positive coefficients `s i` and orthonormal
families `u`, `v` in the two factors. -/
structure IsSchmidtDecomposition {m n r : ℕ} (psi : EuclideanSpace ℂ (Fin m × Fin n))
    (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
    (v : Fin r → EuclideanSpace ℂ (Fin n)) : Prop where
  pos : ∀ i, 0 < s i
  left_orthonormal : Orthonormal ℂ u
  right_orthonormal : Orthonormal ℂ v
  amp : ∀ j k, psi (j, k) = ∑ i, (s i : ℂ) * u i j * v i k

/-! ### The Gram matrix of a decomposition -/

section

variable {m n r : ℕ} {M : Matrix (Fin m) (Fin n) ℂ} {s : Fin r → ℝ}
  {u : Fin r → EuclideanSpace ℂ (Fin m)} {v : Fin r → EuclideanSpace ℂ (Fin n)}

lemma mul_conjTranspose_of_decomp (hv : Orthonormal ℂ v)
    (hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k) :
    M * Mᴴ = ∑ i, ((s i : ℂ) ^ 2) • outer (u i) (u i) := by
  ext j a
  rw [Matrix.mul_apply]
  have expand : ∀ k, M j k * Mᴴ k a
      = ∑ i, ∑ l, ((s i : ℂ) * u i j * v i k) *
          ((s l : ℂ) * (starRingEnd ℂ) (u l a) * (starRingEnd ℂ) (v l k)) := by
    intro k
    rw [Matrix.conjTranspose_apply, hM, hM, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [← starRingEnd_apply, map_mul, Complex.conj_ofReal]
  simp only [expand]
  rw [Finset.sum_comm]
  have key : ∀ i : Fin r, ∑ k, ∑ l, ((s i : ℂ) * u i j * v i k) *
          ((s l : ℂ) * (starRingEnd ℂ) (u l a) * (starRingEnd ℂ) (v l k))
      = ((s i : ℂ) ^ 2) * (u i j * (starRingEnd ℂ) (u i a)) := by
    intro i
    rw [Finset.sum_comm]
    have step : ∀ l : Fin r, ∑ k, ((s i : ℂ) * u i j * v i k) *
          ((s l : ℂ) * (starRingEnd ℂ) (u l a) * (starRingEnd ℂ) (v l k))
        = ((s i : ℂ) * u i j * ((s l : ℂ) * (starRingEnd ℂ) (u l a))) *
            (if i = l then 1 else 0) := by
      intro l
      rw [← sum_conj_of_orthonormal hv i l, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [step]
    simp
    ring
  simp only [key]
  simp [outer, Matrix.sum_apply, smul_eq_mul]

lemma pow_sum_outer (hu : Orthonormal ℂ u) (c : Fin r → ℂ) (k : ℕ) :
    (∑ i, c i • outer (u i) (u i)) ^ (k + 1) = ∑ i, (c i) ^ (k + 1) • outer (u i) (u i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, outer_mul_outer, (orthonormal_iff_ite.mp hu) i i]
      simp [pow_succ]
    · intro l _ hl
      rw [smul_mul_smul_comm, outer_mul_outer, (orthonormal_iff_ite.mp hu) i l,
        if_neg (Ne.symm hl)]
      simp
    · simp

lemma trace_pow_mul_conjTranspose (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k) (k : ℕ) :
    Matrix.trace ((M * Mᴴ) ^ (k + 1)) = ∑ i, (((s i : ℂ) ^ 2)) ^ (k + 1) := by
  rw [mul_conjTranspose_of_decomp hv hM, pow_sum_outer hu, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, trace_outer, (orthonormal_iff_ite.mp hu) i i]
  simp

end

/-! ### Uniqueness of the Schmidt coefficients -/

theorem schmidt_coefficients_unique {m n : ℕ} {psi : EuclideanSpace ℂ (Fin m × Fin n)}
    {r r' : ℕ} {s : Fin r → ℝ} {s' : Fin r' → ℝ}
    {u : Fin r → EuclideanSpace ℂ (Fin m)} {v : Fin r → EuclideanSpace ℂ (Fin n)}
    {u' : Fin r' → EuclideanSpace ℂ (Fin m)} {v' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi s u v) (h' : IsSchmidtDecomposition psi s' u' v') :
    Multiset.map s Finset.univ.val = Multiset.map s' Finset.univ.val := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun j k => psi (j, k) with hMdef
  have hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k := fun j k => h.amp j k
  have hM' : ∀ j k, M j k = ∑ i, (s' i : ℂ) * u' i j * v' i k := fun j k => h'.amp j k
  have hpow : ∀ k : ℕ, 1 ≤ k → (∑ i, ((s i) ^ 2) ^ k) = ∑ i, ((s' i) ^ 2) ^ k := by
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 := trace_pow_mul_conjTranspose h.left_orthonormal h.right_orthonormal hM k
    have h2 := trace_pow_mul_conjTranspose h'.left_orthonormal h'.right_orthonormal hM' k
    have h3 : (∑ i, (((s i : ℂ)) ^ 2) ^ (k + 1)) = ∑ i, (((s' i : ℂ)) ^ 2) ^ (k + 1) := by
      rw [← h1, ← h2]
    exact_mod_cast h3
  have hA : ∀ x ∈ Multiset.map (fun i => (s i) ^ 2) (Finset.univ : Finset (Fin r)).val, 0 < x := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact pow_pos (h.pos i) 2
  have hB : ∀ x ∈ Multiset.map (fun i => (s' i) ^ 2) (Finset.univ : Finset (Fin r')).val, 0 < x := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact pow_pos (h'.pos i) 2
  have hsq : Multiset.map (fun i => (s i) ^ 2) (Finset.univ : Finset (Fin r)).val
      = Multiset.map (fun i => (s' i) ^ 2) (Finset.univ : Finset (Fin r')).val := by
    refine multiset_eq_of_powerSum_eq hA hB fun k hk => ?_
    rw [Multiset.map_map, Multiset.map_map, ← Finset.sum_eq_multiset_sum,
      ← Finset.sum_eq_multiset_sum]
    simpa [Function.comp] using hpow k hk
  have e1 : Multiset.map Real.sqrt (Multiset.map (fun i => (s i) ^ 2)
      (Finset.univ : Finset (Fin r)).val) = Multiset.map s Finset.univ.val := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [Function.comp, Real.sqrt_sq (h.pos i).le]
  have e2 : Multiset.map Real.sqrt (Multiset.map (fun i => (s' i) ^ 2)
      (Finset.univ : Finset (Fin r')).val) = Multiset.map s' Finset.univ.val := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [Function.comp, Real.sqrt_sq (h'.pos i).le]
  rw [← e1, ← e2, hsq]

/-! ### Existence -/

theorem schmidt_exists {m n : ℕ} (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi s u v := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun j k => psi (j, k) with hMdef
  have hA : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  set b := hA.eigenvectorBasis with hbdef
  set mu := hA.eigenvalues with hmudef
  set w : Fin m → Fin n → ℂ := fun i k => ∑ j, (starRingEnd ℂ) (b i j) * M j k with hwdef
  -- the eigenvalue equation, in coordinates
  have heig : ∀ i a, ∑ j, (M * Mᴴ) a j * b i j = (mu i : ℂ) * b i a := by
    intro i a
    have h := congrFun (hA.mulVec_eigenvectorBasis i) a
    simpa [Matrix.mulVec, dotProduct, Complex.real_smul] using h
  -- the vectors `w i` are orthogonal, with squared norms the eigenvalues
  have gram : ∀ i l, ∑ k, (starRingEnd ℂ) (w i k) * w l k
      = (mu i : ℂ) * (if l = i then 1 else 0) := by
    intro i l
    have e0 : ∑ k, (starRingEnd ℂ) (w i k) * w l k
        = ∑ a, (starRingEnd ℂ) (b l a) * ∑ j, (M * Mᴴ) a j * b i j := by
      have e1 : ∀ k, (starRingEnd ℂ) (w i k) * w l k
          = ∑ j, ∑ a, (b i j * (starRingEnd ℂ) (M j k)) * ((starRingEnd ℂ) (b l a) * M a k) := by
        intro k
        rw [hwdef]
        simp only [map_sum, map_mul, Complex.conj_conj]
        rw [Finset.sum_mul_sum]
      simp only [e1]
      rw [Finset.sum_comm]
      have e2 : ∀ j : Fin m, ∑ k, ∑ a, (b i j * (starRingEnd ℂ) (M j k)) *
            ((starRingEnd ℂ) (b l a) * M a k)
          = ∑ a, ∑ k, (b i j * (starRingEnd ℂ) (M j k)) * ((starRingEnd ℂ) (b l a) * M a k) :=
        fun j => Finset.sum_comm
      simp only [e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Matrix.conjTranspose_apply]; ring
    rw [e0]
    simp only [heig]
    have e3 : ∑ a, (starRingEnd ℂ) (b l a) * ((mu i : ℂ) * b i a)
        = (mu i : ℂ) * (inner ℂ (b l) (b i)) := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by simp [RCLike.inner_apply]; ring
    rw [e3, (orthonormal_iff_ite.mp b.orthonormal) l i]
  have hsq : ∀ i, mu i = ∑ k, ‖w i k‖ ^ 2 := by
    intro i
    have h := gram i i
    rw [if_pos rfl, mul_one] at h
    have h2 : (∑ k, (starRingEnd ℂ) (w i k) * w i k) = ((∑ k, ‖w i k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm, Complex.mul_conj']
    rw [h2] at h
    exact_mod_cast h.symm
  have hmupos : ∀ i, 0 ≤ mu i := fun i => by rw [hsq i]; positivity
  have hw0 : ∀ i, mu i = 0 → ∀ k, w i k = 0 := by
    intro i hi k
    have h := hsq i
    rw [hi] at h
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h.symm k
      (Finset.mem_univ k)
    simpa using h3
  have hrecon : ∀ j k, M j k = ∑ i, b i j * w i k := by
    intro j k
    have h := b.sum_repr' (WithLp.toLp 2 (fun j => M j k) : EuclideanSpace ℂ (Fin m))
    have h2 := congrArg (fun (x : EuclideanSpace ℂ (Fin m)) => x j) h
    simp only [PiLp.inner_apply, RCLike.inner_apply] at h2
    simp at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  -- the indices with nonzero eigenvalue
  set S : Finset (Fin m) := Finset.univ.filter (fun i => mu i ≠ 0) with hSdef
  have hmemS : ∀ x, x ∈ S ↔ mu x ≠ 0 := by
    intro x; rw [hSdef, Finset.mem_filter]; simp
  set g : Fin S.card → Fin m := fun i => ((S.equivFin.symm i : {x // x ∈ S}) : Fin m) with hgdef
  have hgne : ∀ i, mu (g i) ≠ 0 := fun i => (hmemS _).mp (S.equivFin.symm i).2
  have hginj : Function.Injective g := by
    intro i j hij
    have h : (S.equivFin.symm i) = (S.equivFin.symm j) := Subtype.ext hij
    simpa using h
  have hgpos : ∀ i, 0 < Real.sqrt (mu (g i)) :=
    fun i => Real.sqrt_pos.mpr (lt_of_le_of_ne (hmupos _) (Ne.symm (hgne i)))
  have hsqrt_ne : ∀ i, ((Real.sqrt (mu (g i)) : ℂ)) ≠ 0 := by
    intro i
    exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt (hgpos i))
  have hsqrt_sq : ∀ i, ((Real.sqrt (mu (g i)) : ℂ)) ^ 2 = (mu (g i) : ℂ) := by
    intro i
    have : Real.sqrt (mu (g i)) ^ 2 = mu (g i) := Real.sq_sqrt (hmupos _)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  refine ⟨S.card, fun i => Real.sqrt (mu (g i)), fun i => b (g i),
    fun i => (WithLp.toLp 2 (fun k => ((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) :
      EuclideanSpace ℂ (Fin n)), hgpos, b.orthonormal.comp g hginj, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i l
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    have hcalc : ∑ k, (starRingEnd ℂ) (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) *
        (((Real.sqrt (mu (g l)) : ℂ))⁻¹ * w (g l) k)
        = ((Real.sqrt (mu (g i)) : ℂ))⁻¹ * ((Real.sqrt (mu (g l)) : ℂ))⁻¹ *
            ((mu (g i) : ℂ) * (if g l = g i then 1 else 0)) := by
      rw [← gram (g i) (g l), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    have hswap : ∑ k, ((Real.sqrt (mu (g l)) : ℂ))⁻¹ * w (g l) k *
        (starRingEnd ℂ) (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k)
        = ∑ k, (starRingEnd ℂ) (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) *
            (((Real.sqrt (mu (g l)) : ℂ))⁻¹ * w (g l) k) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hswap, hcalc]
    by_cases hil : i = l
    · subst hil
      rw [if_pos rfl, if_pos rfl, mul_one]
      field_simp
      rw [hsqrt_sq i, div_self (Complex.ofReal_ne_zero.mpr (hgne i))]
    · rw [if_neg hil, if_neg (fun hc => hil (hginj hc).symm)]
      ring
  · intro j k
    have hzero : ∀ x ∈ (Finset.univ : Finset (Fin m)), x ∉ S → b x j * w x k = 0 := by
      intro x _ hx
      have hx0 : mu x = 0 := by
        by_contra hne
        exact hx ((hmemS x).mpr hne)
      rw [hw0 x hx0 k, mul_zero]
    have step : ∑ i, b i j * w i k = ∑ i : Fin S.card, (Real.sqrt (mu (g i)) : ℂ) * b (g i) j *
        (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) := by
      rw [← Finset.sum_subset (Finset.subset_univ S) hzero,
        ← Finset.sum_coe_sort S (fun i => b i j * w i k),
        ← Equiv.sum_comp (S.equivFin.symm)
          (fun (x : {x // x ∈ S}) => b (x : Fin m) j * w (x : Fin m) k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hgi : ((S.equivFin.symm i : {x // x ∈ S}) : Fin m) = g i := rfl
      rw [hgi]
      calc b (g i) j * w (g i) k
          = (((Real.sqrt (mu (g i)) : ℂ)) * ((Real.sqrt (mu (g i)) : ℂ))⁻¹) *
              (b (g i) j * w (g i) k) := by
            rw [mul_inv_cancel₀ (hsqrt_ne i), one_mul]
        _ = _ := by ring
    have hpsi : psi (j, k) = M j k := rfl
    rw [hpsi, hrecon j k, step]

lemma sum_sq_coeff {m n : ℕ} {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {s : Fin r → ℝ}
    {u : Fin r → EuclideanSpace ℂ (Fin m)} {v : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi s u v) : ∑ i, (s i) ^ 2 = ‖psi‖ ^ 2 := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun j k => psi (j, k) with hMdef
  have hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k := fun j k => h.amp j k
  have h1 := trace_pow_mul_conjTranspose h.left_orthonormal h.right_orthonormal hM 0
  have h2 : Matrix.trace (M * Mᴴ) = ((∑ p : Fin m × Fin n, ‖psi p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hMdef,
      Matrix.of_apply, Fintype.sum_prod_type]
    push_cast
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [← starRingEnd_apply, Complex.mul_conj']
  rw [pow_one, h2] at h1
  simp only [zero_add, pow_one] at h1
  have h3 : (∑ p : Fin m × Fin n, ‖psi p‖ ^ 2) = ∑ i, (s i) ^ 2 := by exact_mod_cast h1
  rw [← h3, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-! ### Main theorem -/

/-- **Schmidt decomposition.** Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` can be written as
`psi = ∑ i, s i • (u i ⊗ v i)` with strictly positive reals `s i` and orthonormal families
`u`, `v`; the sum of the squares of the coefficients is `‖psi‖ ^ 2` (so it is `1` for a
normalized state), and the multiset of Schmidt coefficients is uniquely determined by `psi`. -/
theorem schmidt_decomposition {m n : ℕ} (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)),
      IsSchmidtDecomposition psi s u v ∧
      (∑ i, (s i) ^ 2 = ‖psi‖ ^ 2) ∧
      (∀ (r' : ℕ) (s' : Fin r' → ℝ) (u' : Fin r' → EuclideanSpace ℂ (Fin m))
        (v' : Fin r' → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi s' u' v' →
        Multiset.map s' Finset.univ.val = Multiset.map s Finset.univ.val) := by
  obtain ⟨r, s, u, v, h⟩ := schmidt_exists psi
  exact ⟨r, s, u, v, h, sum_sq_coeff h, fun r' s' u' v' h' =>
    schmidt_coefficients_unique h' h⟩

/-! ### Formulation on the genuine tensor product `ℂ^m ⊗ ℂ^n` -/

open TensorProduct in
/-- The canonical identification of `ℂ^m ⊗ ℂ^n` with amplitudes indexed by pairs. -/
noncomputable def tensorEquiv (m n : ℕ) :
    (EuclideanSpace ℂ (Fin m) ⊗[ℂ] EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin m × Fin n) :=
  ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.tensorProduct
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).equivFun ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Fin m × Fin n → ℂ)).symm

open TensorProduct in
lemma tensorEquiv_tmul {m n : ℕ} (x : EuclideanSpace ℂ (Fin m)) (y : EuclideanSpace ℂ (Fin n))
    (j : Fin m) (k : Fin n) : tensorEquiv m n (x ⊗ₜ[ℂ] y) (j, k) = x j * y k := by
  simp [tensorEquiv, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]

open TensorProduct in
lemma tensorEquiv_apply_of_sum {m n r : ℕ} (s : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ (Fin m)) (v : Fin r → EuclideanSpace ℂ (Fin n))
    (j : Fin m) (k : Fin n) :
    tensorEquiv m n (∑ i, (s i : ℂ) • (u i ⊗ₜ[ℂ] v i)) (j, k)
      = ∑ i, (s i : ℂ) * u i j * v i k := by
  rw [map_sum]
  simp only [map_smul]
  rw [show ((∑ i, (s i : ℂ) • tensorEquiv m n (u i ⊗ₜ[ℂ] v i)) :
      EuclideanSpace ℂ (Fin m × Fin n)) (j, k)
      = ∑ i, (s i : ℂ) * (tensorEquiv m n (u i ⊗ₜ[ℂ] v i)) (j, k) from by simp]
  exact Finset.sum_congr rfl fun i _ => by rw [tensorEquiv_tmul]; ring

open TensorProduct in
/-- **Schmidt decomposition, tensor product form.** Every vector of `ℂ^m ⊗ ℂ^n` is of the form
`∑ i, s i • (u i ⊗ v i)` with `s i > 0` and `u`, `v` orthonormal families, and the multiset of
the coefficients `s` is uniquely determined. -/
theorem schmidt_decomposition_tensor {m n : ℕ}
    (psi : EuclideanSpace ℂ (Fin m) ⊗[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)),
      (∀ i, 0 < s i) ∧ Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      psi = ∑ i, (s i : ℂ) • (u i ⊗ₜ[ℂ] v i) ∧
      (∀ (r' : ℕ) (s' : Fin r' → ℝ) (u' : Fin r' → EuclideanSpace ℂ (Fin m))
        (v' : Fin r' → EuclideanSpace ℂ (Fin n)), (∀ i, 0 < s' i) → Orthonormal ℂ u' →
        Orthonormal ℂ v' → psi = ∑ i, (s' i : ℂ) • (u' i ⊗ₜ[ℂ] v' i) →
        Multiset.map s' Finset.univ.val = Multiset.map s Finset.univ.val) := by
  obtain ⟨r, s, u, v, hd⟩ := schmidt_exists (tensorEquiv m n psi)
  refine ⟨r, s, u, v, hd.pos, hd.left_orthonormal, hd.right_orthonormal, ?_, ?_⟩
  · refine (tensorEquiv m n).injective ?_
    ext p
    rw [tensorEquiv_apply_of_sum]
    exact hd.amp p.1 p.2
  · intro r' s' u' v' hpos' hu' hv' heq
    refine schmidt_coefficients_unique ⟨hpos', hu', hv', ?_⟩ hd
    intro j k
    conv_lhs => rw [heq]
    exact tensorEquiv_apply_of_sum s' u' v' j k

end QI

