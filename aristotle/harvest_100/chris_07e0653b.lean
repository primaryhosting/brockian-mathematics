import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/
noncomputable def tensor (a : EuclideanSpace ℂ (Fin m)) (b : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin m × Fin n) :=
  WithLp.toLp 2 fun p => a p.1 * b p.2

@[simp] lemma tensor_apply (a : EuclideanSpace ℂ (Fin m)) (b : EuclideanSpace ℂ (Fin n))
    (p : Fin m × Fin n) : tensor a b p = a p.1 * b p.2 := rfl

/-- `IsSchmidtDecomposition psi r lam e f` says that the bipartite pure state `psi` is written
as `∑ k, lam k • (e k ⊗ f k)` where the `lam k` are strictly positive reals (the Schmidt
coefficients) and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomposition (psi : EuclideanSpace ℂ (Fin m × Fin n))
    (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
    (f : Fin r → EuclideanSpace ℂ (Fin n)) : Prop where
  coeff_pos : ∀ k, 0 < lam k
  left_orthonormal : Orthonormal ℂ e
  right_orthonormal : Orthonormal ℂ f
  decomp : psi = ∑ k, (lam k : ℂ) • tensor (e k) (f k)

/-- Orthonormality of a family in `EuclideanSpace ℂ (Fin p)` in coordinates. -/
lemma orthonormal_iff_sum {p r : ℕ} (e : Fin r → EuclideanSpace ℂ (Fin p)) :
    Orthonormal ℂ e ↔ ∀ k l, ∑ i, conj (e k i) * e l i = if k = l then 1 else 0 := by
  rw [orthonormal_iff_ite]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The "transposed" form of orthonormality. -/
lemma orthonormal_sum' {p r : ℕ} {e : Fin r → EuclideanSpace ℂ (Fin p)} (he : Orthonormal ℂ e)
    (k l : Fin r) : ∑ i, e k i * conj (e l i) = if k = l then 1 else 0 := by
  rw [orthonormal_iff_sum] at he
  have h2 : ∑ i, e k i * conj (e l i) = conj (∑ i, conj (e k i) * e l i) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rw [h2, he k l]
  by_cases hkl : k = l <;> simp [hkl]

/-- An orthonormal basis of `EuclideanSpace ℂ (Fin m)` extending a given orthonormal family. -/
lemma exists_orthonormalBasis_extend {r : ℕ} (e : Fin r → EuclideanSpace ℂ (Fin m))
    (he : Orthonormal ℂ e) (hr : r ≤ m) :
    ∃ b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)),
      ∀ k : Fin r, b (Fin.castLE hr k) = e k := by
  classical
  set v : Fin m → EuclideanSpace ℂ (Fin m) := fun i => if h : (i:ℕ) < r then e ⟨i, h⟩ else 0
    with hv
  set s : Set (Fin m) := {i | (i:ℕ) < r} with hs
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  have hon : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨i', hi'⟩
    have hi2 : (i:ℕ) < r := hi
    have hi2' : (i':ℕ) < r := hi'
    simp only [Set.restrict_apply, hv, dif_pos hi2, dif_pos hi2']
    rw [orthonormal_iff_ite] at he
    rw [he]
    congr 1
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨b, fun k => ?_⟩
  have hmem : (Fin.castLE hr k) ∈ s := by simp [hs]
  rw [hb _ hmem]
  simp only [hv]
  rw [dif_pos (show ((Fin.castLE hr k : Fin m) : ℕ) < r by simp [k.isLt])]
  congr 1

lemma decomp_apply {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) (i : Fin m) (j : Fin n) :
    psi (i, j) = ∑ k, (lam k : ℂ) * e k i * f k j := by
  rw [h.decomp]
  simp [tensor, mul_assoc]

/-- The (unnormalised) reduced density matrix of `psi` on the first factor. -/
noncomputable def rho (psi : EuclideanSpace ℂ (Fin m × Fin n)) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i i' => ∑ j, psi (i, j) * conj (psi (i', j))

lemma rho_eq_sum {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) :
    rho psi = Matrix.of fun i i' => ∑ k, ((lam k : ℂ) ^ 2) * e k i * conj (e k i') := by
  have hf : ∀ k l, ∑ j, conj (f k j) * f l j = if k = l then 1 else 0 :=
    (orthonormal_iff_sum f).1 h.right_orthonormal
  ext i i'
  simp only [rho, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => by
    rw [decomp_apply h i j, decomp_apply h i' j])]
  have key : ∀ k l : Fin r, ∑ j, f k j * conj (f l j) = if k = l then (1:ℂ) else 0 :=
    orthonormal_sum' h.right_orthonormal
  calc (∑ j, (∑ k, (lam k : ℂ) * e k i * f k j) * conj (∑ l, (lam l : ℂ) * e l i' * f l j))
      = ∑ j, ∑ k, ∑ l, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
          * (f k j * conj (f l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∑ k, ∑ l, ((lam k : ℂ) * e k i * ((lam l : ℂ) * conj (e l i')))
          * (∑ j, f k j * conj (f l j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k, ((lam k : ℂ) ^ 2) * e k i * conj (e k i') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => by rw [key k l])]
        simp
        ring

lemma schmidt_rank_le {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) : r ≤ m := by
  simpa using h.left_orthonormal.linearIndependent.fintype_card_le_finrank (R := ℂ)

/-- Splitting `Fin m` as `Fin r ⊕ Fin (m - r)`. -/
noncomputable def finSplit {r m : ℕ} (hr : r ≤ m) : Fin r ⊕ Fin (m - r) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hr))

lemma finSplit_inl {r m : ℕ} (hr : r ≤ m) (k : Fin r) :
    finSplit hr (Sum.inl k) = Fin.castLE hr k := by
  ext; simp [finSplit]

lemma finSplit_inr_val {r m : ℕ} (hr : r ≤ m) (l : Fin (m - r)) :
    ((finSplit hr (Sum.inr l) : Fin m) : ℕ) = r + l := by simp [finSplit]

lemma sum_finSplit {M : Type*} [AddCommMonoid M] {r m : ℕ} (hr : r ≤ m) (g : Fin m → M) :
    ∑ j, g j =
      (∑ k : Fin r, g (Fin.castLE hr k)) + ∑ l : Fin (m - r), g (finSplit hr (Sum.inr l)) := by
  rw [← Equiv.sum_comp (finSplit hr) g, Fintype.sum_sum_type]
  simp only [finSplit_inl]

lemma prod_finSplit {M : Type*} [CommMonoid M] {r m : ℕ} (hr : r ≤ m) (g : Fin m → M) :
    ∏ j, g j =
      (∏ k : Fin r, g (Fin.castLE hr k)) * ∏ l : Fin (m - r), g (finSplit hr (Sum.inr l)) := by
  rw [← Equiv.prod_comp (finSplit hr) g, Fintype.prod_sum_type]
  simp only [finSplit_inl]

/-- The characteristic polynomial of the reduced density matrix, computed from a Schmidt
decomposition. -/
lemma charpoly_rho {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) :
    (rho psi).charpoly = X ^ (m - r) * ∏ k : Fin r, (X - C ((lam k : ℂ) ^ 2)) := by
  classical
  have hr := schmidt_rank_le h
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extend e h.left_orthonormal hr
  set U : Matrix (Fin m) (Fin m) ℂ := Matrix.of (fun i j => b j i) with hU
  set d : Fin m → ℂ := fun j => if hj : (j : ℕ) < r then ((lam ⟨j, hj⟩ : ℝ) : ℂ) ^ 2 else 0
    with hd
  have hdcast : ∀ k : Fin r, d (Fin.castLE hr k) = ((lam k : ℂ)) ^ 2 := by
    intro k
    simp only [hd]
    rw [dif_pos (show ((Fin.castLE hr k : Fin m) : ℕ) < r by simp [k.isLt])]
    simp
  have hdinr : ∀ l : Fin (m - r), d (finSplit hr (Sum.inr l)) = 0 := by
    intro l
    simp only [hd]
    rw [dif_neg]
    simp [finSplit_inr_val]
  have hUU : Uᴴ * U = 1 := by
    ext j j'
    rw [Matrix.mul_apply]
    simp only [hU, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
      Matrix.one_apply]
    exact (orthonormal_iff_sum (⇑b)).1 b.orthonormal j j'
  have hrho : rho psi = U * Matrix.diagonal d * Uᴴ := by
    rw [rho_eq_sum h]
    ext i i'
    simp only [Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def, hU,
      Matrix.of_apply]
    rw [sum_finSplit hr (fun j => b j i * d j * conj (b j i'))]
    simp only [hdcast, hdinr, hb, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrho, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one,
    Matrix.charpoly_diagonal, prod_finSplit hr (fun j => X - C (d j))]
  simp only [hdcast, hdinr, map_zero, sub_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

lemma roots_charpoly_rho {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) :
    (rho psi).charpoly.roots =
      Multiset.replicate (m - r) 0 + Finset.univ.val.map (fun k => ((lam k : ℂ) ^ 2)) := by
  rw [charpoly_rho h]
  set a : Fin r → ℂ := fun k => ((lam k : ℂ) ^ 2) with ha
  have hprod : (∏ k : Fin r, ((X : ℂ[X]) - C (a k)))
      = (Multiset.map (fun x => X - C x) (Finset.univ.val.map a)).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  have h1 : ((X : ℂ[X]) ^ (m - r)) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : (∏ k : Fin r, ((X : ℂ[X]) - C (a k))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => X_sub_C_ne_zero _
  rw [Polynomial.roots_mul (mul_ne_zero h1 h2), Polynomial.roots_pow, Polynomial.roots_X, hprod,
    Polynomial.roots_multiset_prod_X_sub_C]
  congr 1
  simp [Multiset.nsmul_singleton]

/-- Existence of a Schmidt decomposition. -/
lemma exists_schmidtDecomposition (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi r lam e f := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of (fun i j => psi (i, j)) with hM
  set A : Matrix (Fin n) (Fin n) ℂ := Mᴴ * M with hAdef
  have hPSD : A.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hA : A.IsHermitian := hPSD.isHermitian
  set mu := hA.eigenvalues with hmu
  have hmu0 : ∀ j, 0 ≤ mu j := fun j => hPSD.eigenvalues_nonneg j
  set V := hA.eigenvectorBasis with hV
  have hAV : ∀ j, A *ᵥ (V j).ofLp = mu j • (V j).ofLp := fun j => hA.mulVec_eigenvectorBasis j
  set w : Fin n → (Fin m → ℂ) := fun j => M *ᵥ (V j).ofLp with hw
  have hVon : ∀ j l, star ((V j).ofLp) ⬝ᵥ ((V l).ofLp) = if j = l then (1 : ℂ) else 0 := by
    intro j l
    have := (orthonormal_iff_ite (𝕜 := ℂ)).1 V.orthonormal j l
    simpa [dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using this
  have key : ∀ j l, star (w j) ⬝ᵥ (w l) = (mu l : ℂ) * (if j = l then 1 else 0) := by
    intro j l
    simp only [hw]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hAdef, hAV l]
    rw [show star ((V j).ofLp) ⬝ᵥ (mu l • (V l).ofLp)
          = (mu l : ℂ) * (star ((V j).ofLp) ⬝ᵥ ((V l).ofLp)) by
      simp only [dotProduct, Complex.real_smul, Pi.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    rw [hVon]
  -- vectors with vanishing eigenvalue contribute nothing
  have hwzero : ∀ p : Fin n, mu p = 0 → w p = 0 := by
    intro p hp
    have := key p p
    rw [hp] at this
    simpa using dotProduct_star_self_eq_zero.1 (by simpa using this)
  -- completeness of the eigenbasis
  have hcomplete : ∀ q j : Fin n, ∑ p, V p q * conj (V p j) = if q = j then (1 : ℂ) else 0 := by
    intro q j
    set P : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun q p => V p q) with hP
    have hPP : Pᴴ * P = 1 := by
      ext p p'
      rw [Matrix.mul_apply]
      simp only [hP, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
        Matrix.one_apply]
      exact (orthonormal_iff_sum (⇑V)).1 V.orthonormal p p'
    have hPP' : P * Pᴴ = 1 := mul_eq_one_comm.2 hPP
    have := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N q j) hPP'
    simpa [Matrix.mul_apply, hP, Matrix.one_apply] using this
  -- reconstruction of `M` from the eigenbasis
  have hrecon : ∀ (i : Fin m) (j : Fin n), ∑ p, w p i * conj (V p j) = M i j := by
    intro i j
    have : ∀ p : Fin n, w p i * conj (V p j) = ∑ q, M i q * (V p q * conj (V p j)) := by
      intro p
      simp only [hw, Matrix.mulVec, dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => this p), Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => by
      rw [← Finset.mul_sum, hcomplete q j])]
    simp
  -- index the nonzero eigenvalues
  set S := {j : Fin n // mu j ≠ 0} with hS
  set r := Fintype.card S with hr
  set eqv : Fin r ≃ S := (Fintype.equivFin S).symm with heqv
  set idx : Fin r → Fin n := fun k => (eqv k).1 with hidx
  have hidxinj : Function.Injective idx :=
    fun k l hkl => eqv.injective (Subtype.ext hkl)
  have hidxpos : ∀ k, 0 < mu (idx k) := fun k => lt_of_le_of_ne (hmu0 _) (Ne.symm (eqv k).2)
  set lam : Fin r → ℝ := fun k => Real.sqrt (mu (idx k)) with hlam
  have hlampos : ∀ k, 0 < lam k := fun k => Real.sqrt_pos.2 (hidxpos k)
  have hlamsq : ∀ k, (lam k) ^ 2 = mu (idx k) := fun k => Real.sq_sqrt (hmu0 _)
  set c : Fin r → ℂ := fun k => ((lam k : ℝ) : ℂ)⁻¹ with hc
  have hcne : ∀ k, ((lam k : ℝ) : ℂ) ≠ 0 := fun k => by
    simpa using (hlampos k).ne'
  set e : Fin r → EuclideanSpace ℂ (Fin m) :=
    fun k => WithLp.toLp 2 (fun i => c k * w (idx k) i) with he
  set f : Fin r → EuclideanSpace ℂ (Fin n) :=
    fun k => WithLp.toLp 2 (fun j => conj (V (idx k) j)) with hf
  refine ⟨r, lam, e, f, ?_, ?_, ?_, ?_⟩
  · exact hlampos
  · rw [orthonormal_iff_sum]
    intro k l
    have hkey := key (idx k) (idx l)
    have hexp : ∑ i, conj (e k i) * e l i
        = conj (c k) * c l * (star (w (idx k)) ⬝ᵥ (w (idx l))) := by
      simp only [he, dotProduct, Pi.star_apply, RCLike.star_def, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp, hkey]
    have hck : conj (c k) = c k := by simp [hc, ← Complex.ofReal_inv]
    rw [hck]
    by_cases hkl : k = l
    · subst hkl
      have h1 : (if idx k = idx k then (1 : ℂ) else 0) = 1 := if_pos rfl
      have h2 : (if k = k then (1 : ℂ) else 0) = 1 := if_pos rfl
      rw [h1, h2, mul_one, ← hlamsq k]
      simp only [hc]
      push_cast
      field_simp
      exact div_self (hcne k)
    · rw [if_neg (fun hh => hkl (hidxinj hh)), if_neg hkl]
      ring
  · rw [orthonormal_iff_sum]
    intro k l
    have : ∑ j, conj (f k j) * f l j = ∑ j, V (idx k) j * conj (V (idx l) j) := by
      simp only [hf]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [this, orthonormal_sum' V.orthonormal (idx k) (idx l)]
    by_cases hkl : k = l
    · rw [if_pos (by rw [hkl]), if_pos hkl]
    · rw [if_neg (fun hh => hkl (hidxinj hh)), if_neg hkl]
  · apply PiLp.ext
    intro p
    obtain ⟨i, j⟩ := p
    have hsumval : (∑ k, (lam k : ℂ) • tensor (e k) (f k)) (i, j)
        = ∑ k, (lam k : ℂ) * (e k i * f k j) := by
      simp [tensor]
    rw [hsumval]
    have hterm : ∀ k : Fin r, (lam k : ℂ) * (e k i * f k j)
        = w (idx k) i * conj (V (idx k) j) := by
      intro k
      have hinv : ((lam k : ℝ) : ℂ)⁻¹ * ((lam k : ℝ) : ℂ) = 1 := inv_mul_cancel₀ (hcne k)
      simp only [he, hf, hc]
      field_simp
      linear_combination (w (idx k) i * conj (V (idx k) j)) * hinv
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
    -- extend the sum to all of `Fin n`
    have hext : ∑ k : Fin r, w (idx k) i * conj (V (idx k) j)
        = ∑ p : Fin n, w p i * conj (V p j) := by
      have h1 : ∑ k : Fin r, w (idx k) i * conj (V (idx k) j)
          = ∑ s : S, w (s : Fin n) i * conj (V (s : Fin n) j) :=
        Equiv.sum_comp eqv (fun s : S => w (s : Fin n) i * conj (V (s : Fin n) j))
      have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n => mu p ≠ 0),
            w p i * conj (V p j)
          = ∑ s : S, w (s : Fin n) i * conj (V (s : Fin n) j) :=
        Finset.sum_subtype _ (fun x => by simp) _
      rw [h1, ← h2]
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro p _ hp
      have : mu p = 0 := by simpa using hp
      rw [hwzero p this]
      simp
    rw [hext, hrecon i j]
    simp [hM]

/-- Uniqueness of the Schmidt coefficients, as a multiset. -/
lemma schmidt_coefficients_unique {psi : EuclideanSpace ℂ (Fin m × Fin n)}
    {r : ℕ} {lam : Fin r → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)}
    {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {r' : ℕ} {lam' : Fin r' → ℝ} {e' : Fin r' → EuclideanSpace ℂ (Fin m)}
    {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f)
    (h' : IsSchmidtDecomposition psi r' lam' e' f') :
    Finset.univ.val.map lam = Finset.univ.val.map lam' := by
  classical
  have H : Multiset.replicate (m - r) (0 : ℂ) + Finset.univ.val.map (fun k => ((lam k : ℂ) ^ 2))
      = Multiset.replicate (m - r') (0 : ℂ)
        + Finset.univ.val.map (fun k => ((lam' k : ℂ) ^ 2)) := by
    rw [← roots_charpoly_rho h, ← roots_charpoly_rho h']
  set A : Multiset ℂ := Finset.univ.val.map (fun k => ((lam k : ℂ) ^ 2)) with hA
  set B : Multiset ℂ := Finset.univ.val.map (fun k => ((lam' k : ℂ) ^ 2)) with hB
  have hA0 : (0 : ℂ) ∉ A := by
    simp only [hA, Multiset.mem_map]
    rintro ⟨k, -, hk⟩
    exact pow_ne_zero 2 (by simpa using (h.coeff_pos k).ne') hk
  have hB0 : (0 : ℂ) ∉ B := by
    simp only [hB, Multiset.mem_map]
    rintro ⟨k, -, hk⟩
    exact pow_ne_zero 2 (by simpa using (h'.coeff_pos k).ne') hk
  have hAB : A = B := by
    ext z
    rcases eq_or_ne z 0 with rfl | hz
    · rw [Multiset.count_eq_zero.2 hA0, Multiset.count_eq_zero.2 hB0]
    · simpa [Multiset.count_replicate, hz, Ne.symm hz] using congrArg (Multiset.count z) H
  have hfun : (fun z : ℂ => Real.sqrt z.re) ∘ (fun k => ((lam k : ℂ) ^ 2)) = lam := by
    funext k
    simp [Function.comp, ← Complex.ofReal_pow, Real.sqrt_sq (h.coeff_pos k).le]
  have hfun' : (fun z : ℂ => Real.sqrt z.re) ∘ (fun k => ((lam' k : ℂ) ^ 2)) = lam' := by
    funext k
    simp [Function.comp, ← Complex.ofReal_pow, Real.sqrt_sq (h'.coeff_pos k).le]
  have := congrArg (Multiset.map (fun z : ℂ => Real.sqrt z.re)) hAB
  rwa [hA, hB, Multiset.map_map, Multiset.map_map, hfun, hfun'] at this

/-- **Schmidt decomposition.**  Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` admits a Schmidt
decomposition `psi = ∑ k, lam k • (e k ⊗ f k)` with strictly positive coefficients `lam k` and
orthonormal families `e`, `f`; moreover the multiset of Schmidt coefficients is uniquely
determined by `psi`. -/
theorem schmidt_decomposition (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    (∃ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi r lam e f) ∧
    (∀ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n))
      (r' : ℕ) (lam' : Fin r' → ℝ) (e' : Fin r' → EuclideanSpace ℂ (Fin m))
      (f' : Fin r' → EuclideanSpace ℂ (Fin n)),
      IsSchmidtDecomposition psi r lam e f → IsSchmidtDecomposition psi r' lam' e' f' →
      Finset.univ.val.map lam = Finset.univ.val.map lam') :=
  ⟨exists_schmidtDecomposition psi, fun _ _ _ _ _ _ _ _ h h' =>
    schmidt_coefficients_unique h h'⟩

end QI

