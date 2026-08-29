import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace QI

open Finset Matrix

variable {m n : ℕ}

/-- `IsSchmidtDecomp psi s e f` says that the bipartite pure state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, written as its coordinate array) has the Schmidt decomposition
`psi = ∑ k, s k • (e k ⊗ f k)`, where the Schmidt coefficients `s k` are strictly positive
and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomp {ι : Type} [Fintype ι] (psi : Fin m → Fin n → ℂ)
    (s : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m)) (f : ι → EuclideanSpace ℂ (Fin n)) :
    Prop where
  coeff_pos : ∀ k, 0 < s k
  orthonormal_left : Orthonormal ℂ e
  orthonormal_right : Orthonormal ℂ f
  decomp : ∀ i j, psi i j = ∑ k, (s k : ℂ) * e k i * f k j

/-- The self-adjoint operator `∑ k, c k • ⟪e k, ·⟫ • e k`. -/
noncomputable def specOp {ι : Type} [Fintype ι] (c : ι → ℝ)
    (e : ι → EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  ∑ k, (c k : ℂ) • (LinearMap.smulRight ((innerSL ℂ (e k)) : _ →ₗ[ℂ] ℂ) (e k))

lemma specOp_apply {ι : Type} [Fintype ι] (c : ι → ℝ)
    (e : ι → EuclideanSpace ℂ (Fin m)) (v : EuclideanSpace ℂ (Fin m)) :
    specOp c e v = ∑ k, (c k : ℂ) • ((inner ℂ (e k) v : ℂ) • e k) := by
  simp [specOp, LinearMap.sum_apply]

/-- The eigenspace of `specOp c e` for a nonzero eigenvalue `t` is spanned by the `e k`
with `c k = t`; hence its dimension is the multiplicity of `t` in `c`. -/
lemma finrank_ker_specOp {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (e : ι → EuclideanSpace ℂ (Fin m)) (he : Orthonormal ℂ e) (t : ℝ) (ht : t ≠ 0) :
    Module.finrank ℂ
        (LinearMap.ker (specOp c e - (t : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] _)))
      = (univ.filter (fun k => c k = t)).card := by
  classical
  have hij : ∀ j k, (inner ℂ (e j) (e k) : ℂ) = if j = k then 1 else 0 :=
    orthonormal_iff_ite.mp he
  have hTe : ∀ (j : ι) (v : EuclideanSpace ℂ (Fin m)),
      (inner ℂ (e j) (specOp c e v) : ℂ) = (c j : ℂ) * inner ℂ (e j) v := by
    intro j v
    rw [specOp_apply, inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right, inner_smul_right, hij j j, if_pos rfl]; ring
    · intro l _ hl
      rw [inner_smul_right, inner_smul_right, hij j l, if_neg (Ne.symm hl)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  have hker : LinearMap.ker
        (specOp c e - (t : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] _))
      = Submodule.span ℂ (Set.range (e ∘ (Subtype.val : {k : ι // c k = t} → ι))) := by
    apply le_antisymm
    · intro v hv
      have hv' : specOp c e v = (t : ℂ) • v := by
        have h := LinearMap.mem_ker.mp hv
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          sub_eq_zero] at h
        exact h
      have hzero : ∀ j, c j ≠ t → (inner ℂ (e j) v : ℂ) = 0 := by
        intro j hj
        have h1 : (c j : ℂ) * inner ℂ (e j) v = (t : ℂ) * inner ℂ (e j) v := by
          rw [← hTe j v, hv', inner_smul_right]
        have h2 : ((c j : ℂ) - t) * inner ℂ (e j) v = 0 := by linear_combination h1
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd (by exact_mod_cast sub_eq_zero.mp h) hj
        · exact h
      have hrep : v = (t : ℂ)⁻¹ • ∑ k, (c k : ℂ) • ((inner ℂ (e k) v : ℂ) • e k) := by
        rw [← specOp_apply, hv', smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht), one_smul]
      rw [hrep]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => ?_)
      by_cases hk : c k = t
      · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
      · rw [hzero k hk]; simp
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, Function.comp_apply]
      rw [specOp_apply, Finset.sum_eq_single k.1]
      · rw [hij k.1 k.1, if_pos rfl, smul_smul, mul_one, k.2]
      · intro l _ hl; rw [hij l k.1, if_neg hl]; simp
      · intro h; exact absurd (Finset.mem_univ k.1) h
  rw [hker, finrank_span_eq_card (he.comp _ Subtype.val_injective).linearIndependent,
    Fintype.card_subtype]

/-- Two families of strictly positive coefficients defining the same operator agree
as multisets. -/
lemma multiset_map_eq_of_specOp_eq {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (c : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m))
    (c' : ι' → ℝ) (e' : ι' → EuclideanSpace ℂ (Fin m))
    (he : Orthonormal ℂ e) (he' : Orthonormal ℂ e')
    (hc : ∀ k, 0 < c k) (hc' : ∀ k, 0 < c' k)
    (h : specOp c e = specOp c' e') :
    (univ : Finset ι).val.map c = (univ : Finset ι').val.map c' := by
  classical
  have key : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → ℝ) (a : ℝ),
      (Multiset.filter (fun k => a = d k) (univ : Finset κ).val).card
        = (univ.filter (fun k => d k = a)).card := by
    intro κ _ _ d a
    rw [← Finset.filter_val]
    congr 2
    exact Finset.filter_congr (fun k _ => eq_comm)
  refine Multiset.ext.mpr fun a => ?_
  rw [Multiset.count_map, Multiset.count_map, key c a, key c' a]
  rcases lt_or_ge 0 a with ha | ha
  · have h1 := finrank_ker_specOp c e he a (ne_of_gt ha)
    have h2 := finrank_ker_specOp c' e' he' a (ne_of_gt ha)
    rw [← h1, ← h2, h]
  · rw [Finset.filter_false_of_mem
        (fun k _ => by have h1 := hc k; intro hk; rw [hk] at h1; linarith),
      Finset.filter_false_of_mem
        (fun k _ => by have h1 := hc' k; intro hk; rw [hk] at h1; linarith)]
    rfl

/-- The reduced density matrix of `psi` computed from a Schmidt decomposition. -/
lemma IsSchmidtDecomp.reduced {ι : Type} [Fintype ι] {psi : Fin m → Fin n → ℂ}
    {s : ι → ℝ} {e : ι → EuclideanSpace ℂ (Fin m)} {f : ι → EuclideanSpace ℂ (Fin n)}
    (H : IsSchmidtDecomp psi s e f) (i i' : Fin m) :
    ∑ j, psi i j * (starRingEnd ℂ) (psi i' j)
      = ∑ k, (((s k) ^ 2 : ℝ) : ℂ) * (e k i * (starRingEnd ℂ) (e k i')) := by
  classical
  have hfo : ∀ k l, ∑ j, f k j * (starRingEnd ℂ) (f l j) = if l = k then 1 else 0 := by
    intro k l
    have h := (orthonormal_iff_ite.mp H.orthonormal_right) l k
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    rw [← h]
  calc ∑ j, psi i j * (starRingEnd ℂ) (psi i' j)
      = ∑ j, ∑ k, ∑ l, ((s k : ℂ) * e k i * ((s l : ℂ) * (starRingEnd ℂ) (e l i')))
          * (f k j * (starRingEnd ℂ) (f l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [H.decomp i j, H.decomp i' j, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∑ k, ∑ l, ((s k : ℂ) * e k i * ((s l : ℂ) * (starRingEnd ℂ) (e l i')))
          * ∑ j, (f k j * (starRingEnd ℂ) (f l j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
    _ = ∑ k, (((s k) ^ 2 : ℝ) : ℂ) * (e k i * (starRingEnd ℂ) (e k i')) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single k]
        · rw [hfo k k, if_pos rfl]; push_cast; ring
        · intro l _ hl; rw [hfo k l, if_neg hl, mul_zero]
        · intro h; exact absurd (Finset.mem_univ k) h

/-- The operator `specOp (s ^ 2) e` attached to a Schmidt decomposition is the reduced
density operator of `psi`, which does not depend on the decomposition. -/
lemma IsSchmidtDecomp.specOp_apply_eq {ι : Type} [Fintype ι] {psi : Fin m → Fin n → ℂ}
    {s : ι → ℝ} {e : ι → EuclideanSpace ℂ (Fin m)} {f : ι → EuclideanSpace ℂ (Fin n)}
    (H : IsSchmidtDecomp psi s e f) (v : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    specOp (fun k => (s k) ^ 2) e v i
      = ∑ i', (∑ j, psi i j * (starRingEnd ℂ) (psi i' j)) * v i' := by
  classical
  have hinner : ∀ k, (inner ℂ (e k) v : ℂ) = ∑ i', (starRingEnd ℂ) (e k i') * v i' := by
    intro k
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl fun i' _ => mul_comm _ _
  have step : specOp (fun k => (s k) ^ 2) e v i
      = ∑ k, ∑ i', ((((s k) ^ 2 : ℝ) : ℂ) * (e k i * (starRingEnd ℂ) (e k i'))) * v i' := by
    rw [specOp_apply]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hinner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  rw [step, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i' _ => by rw [H.reduced i i', Finset.sum_mul]

/-- The Schmidt coefficients of a state satisfy `∑ k, (s k)^2 = ‖psi‖^2`; in particular, for a
normalised (pure) state the squared Schmidt coefficients sum to `1`. -/
lemma IsSchmidtDecomp.sum_coeff_sq {ι : Type} [Fintype ι] {psi : Fin m → Fin n → ℂ}
    {s : ι → ℝ} {e : ι → EuclideanSpace ℂ (Fin m)} {f : ι → EuclideanSpace ℂ (Fin n)}
    (H : IsSchmidtDecomp psi s e f) :
    ∑ k, (s k) ^ 2 = ∑ i, ∑ j, ‖psi i j‖ ^ 2 := by
  classical
  have hee : ∀ k, ∑ i, e k i * (starRingEnd ℂ) (e k i) = (1 : ℂ) := by
    intro k
    have h := (orthonormal_iff_ite.mp H.orthonormal_left) k k
    rw [PiLp.inner_apply, if_pos rfl] at h
    simp only [RCLike.inner_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have key : ((∑ i, ∑ j, ‖psi i j‖ ^ 2 : ℝ) : ℂ) = ((∑ k, (s k) ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc ∑ i, ∑ j, (‖psi i j‖ : ℂ) ^ 2
        = ∑ i, ∑ j, psi i j * (starRingEnd ℂ) (psi i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            (Complex.mul_conj' (psi i j)).symm
      _ = ∑ i, ∑ k, (((s k) ^ 2 : ℝ) : ℂ) * (e k i * (starRingEnd ℂ) (e k i)) :=
          Finset.sum_congr rfl fun i _ => H.reduced i i
      _ = ∑ k, (((s k) ^ 2 : ℝ) : ℂ) * ∑ i, (e k i * (starRingEnd ℂ) (e k i)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
      _ = ∑ k, ((s k : ℂ)) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hee k, mul_one]
          push_cast
          ring
  exact_mod_cast key.symm

/-- Reindexing a Schmidt decomposition along an equivalence. -/
lemma IsSchmidtDecomp.reindex {ι κ : Type} [Fintype ι] [Fintype κ] (E : κ ≃ ι)
    {psi : Fin m → Fin n → ℂ} {s : ι → ℝ} {e : ι → EuclideanSpace ℂ (Fin m)}
    {f : ι → EuclideanSpace ℂ (Fin n)} (H : IsSchmidtDecomp psi s e f) :
    IsSchmidtDecomp psi (s ∘ E) (e ∘ E) (f ∘ E) where
  coeff_pos k := H.coeff_pos (E k)
  orthonormal_left := H.orthonormal_left.comp E E.injective
  orthonormal_right := H.orthonormal_right.comp E E.injective
  decomp i j := by
    rw [H.decomp i j]
    exact (Equiv.sum_comp E (fun k => (s k : ℂ) * e k i * f k j)).symm

/-- **Existence** of the Schmidt decomposition. -/
theorem exists_schmidt (psi : Fin m → Fin n → ℂ) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp psi s e f := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of psi with hMdef
  have hps : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  set hH : (M * Mᴴ).IsHermitian := hps.1 with hHdef
  set mu : Fin m → ℝ := hH.eigenvalues with hmudef
  set u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) := hH.eigenvectorBasis with hudef
  have hmu0 : ∀ i, 0 ≤ mu i := hps.eigenvalues_nonneg
  have heig : ∀ i, (M * Mᴴ) *ᵥ (u i).ofLp = mu i • (u i).ofLp := hH.mulVec_eigenvectorBasis
  -- the (unnormalised) vectors in the second factor
  set F : Fin m → Fin n → ℂ := fun k j => ∑ i, M i j * (starRingEnd ℂ) (u k i) with hFdef
  have hHe : ∀ a b, (starRingEnd ℂ) ((M * Mᴴ) a b) = (M * Mᴴ) b a := by
    intro a b
    conv_rhs => rw [← hH]
    rfl
  have hstep : ∀ l i, ∑ i', (M * Mᴴ) i' i * (starRingEnd ℂ) (u l i')
      = (mu l : ℂ) * (starRingEnd ℂ) (u l i) := by
    intro l i
    have key : ∑ i', (M * Mᴴ) i i' * (u l i') = (mu l : ℂ) * u l i := by
      have h := congrFun (heig l) i
      simpa [Matrix.mulVec, dotProduct] using h
    have h2 := congrArg (starRingEnd ℂ) key
    rw [map_sum, map_mul, Complex.conj_ofReal] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i' _ => by rw [map_mul, hHe i i']
  have hMM : ∀ i i', ∑ j, (starRingEnd ℂ) (M i j) * M i' j = (M * Mᴴ) i' i := by
    intro i i'
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by
      simp [Matrix.conjTranspose_apply, mul_comm]
  have huu : ∀ k l, ∑ i, u k i * (starRingEnd ℂ) (u l i) = if k = l then 1 else 0 := by
    intro k l
    have h := orthonormal_iff_ite.mp u.orthonormal l k
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    rw [h]
    simp [eq_comm]
  have hFF : ∀ k l, ∑ j, (starRingEnd ℂ) (F k j) * F l j
      = (mu l : ℂ) * (if k = l then 1 else 0) := by
    intro k l
    calc ∑ j, (starRingEnd ℂ) (F k j) * F l j
        = ∑ j, ∑ i, ∑ i', (u k i * (starRingEnd ℂ) (u l i')) *
            ((starRingEnd ℂ) (M i j) * M i' j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hFdef]
          simp only
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          simp only [map_mul, Complex.conj_conj]
          ring
      _ = ∑ i, ∑ i', (u k i * (starRingEnd ℂ) (u l i')) *
            ∑ j, ((starRingEnd ℂ) (M i j) * M i' j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i' _ => by rw [Finset.mul_sum]
      _ = ∑ i, u k i * ∑ i', (M * Mᴴ) i' i * (starRingEnd ℂ) (u l i') := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by rw [hMM i i']; ring
      _ = (mu l : ℂ) * ∑ i, u k i * (starRingEnd ℂ) (u l i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hstep l i]; ring
      _ = (mu l : ℂ) * (if k = l then 1 else 0) := by rw [huu k l]
  have hFzero : ∀ k, mu k = 0 → ∀ j, F k j = 0 := by
    intro k hk j
    have h := hFF k k
    rw [if_pos rfl, mul_one, hk, Complex.ofReal_zero] at h
    have h2 : ∑ j, ((Complex.normSq (F k j) : ℝ) : ℂ) = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => Complex.normSq_eq_conj_mul_self
    have h4 : ∑ j, Complex.normSq (F k j) = 0 := by exact_mod_cast h2
    have h5 : Complex.normSq (F k j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp h4 j
        (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp h5
  -- the Schmidt decomposition indexed by the strictly positive eigenvalues
  have key : IsSchmidtDecomp psi (fun k : {k : Fin m // 0 < mu k} => Real.sqrt (mu k.1))
      (fun k => u k.1)
      (fun k => (WithLp.toLp 2 (fun j => ((Real.sqrt (mu k.1) : ℂ))⁻¹ * F k.1 j) :
        EuclideanSpace ℂ (Fin n))) := by
    have hsq : ∀ k : {k : Fin m // 0 < mu k}, 0 < Real.sqrt (mu k.1) :=
      fun k => Real.sqrt_pos.mpr k.2
    refine ⟨hsq, u.orthonormal.comp _ Subtype.val_injective, ?_, ?_⟩
    · refine orthonormal_iff_ite.mpr fun k l => ?_
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply]
      have : ∀ j, (((Real.sqrt (mu l.1) : ℂ))⁻¹ * F l.1 j) *
          (starRingEnd ℂ) (((Real.sqrt (mu k.1) : ℂ))⁻¹ * F k.1 j)
          = ((Real.sqrt (mu k.1) : ℂ))⁻¹ * ((Real.sqrt (mu l.1) : ℂ))⁻¹ *
            ((starRingEnd ℂ) (F k.1 j) * F l.1 j) := by
        intro j
        simp only [map_mul, map_inv₀, Complex.conj_ofReal]
        ring
      rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, hFF k.1 l.1]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, mul_one]
        have h1 : ((Real.sqrt (mu k.1) : ℂ)) ≠ 0 := by
          exact_mod_cast ne_of_gt (hsq k)
        field_simp
        rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt k.2)]
      · rw [if_neg hkl, if_neg (fun h : k.1 = l.1 => hkl (Subtype.ext h))]
        ring
    · intro i j
      have h1 : ∑ k : {k : Fin m // 0 < mu k},
          ((Real.sqrt (mu k.1) : ℝ) : ℂ) * u k.1 i *
            (((Real.sqrt (mu k.1) : ℂ))⁻¹ * F k.1 j)
          = ∑ k : {k : Fin m // 0 < mu k}, u k.1 i * F k.1 j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have h1 : ((Real.sqrt (mu k.1) : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt (hsq k)
        field_simp
      have h2 : ∑ k : {k : Fin m // 0 < mu k}, u k.1 i * F k.1 j
          = ∑ k : Fin m, u k i * F k j := by
        rw [← Finset.sum_subtype (univ.filter (fun k => 0 < mu k))
          (fun x => by simp) (fun k => u k i * F k j)]
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro k _ hk
        have : mu k = 0 := le_antisymm (by simpa using (not_lt.mp (by simpa using hk))) (hmu0 k)
        rw [hFzero k this j, mul_zero]
      have h3 : ∑ k : Fin m, u k i * F k j = psi i j := by
        have : ∀ k, u k i * F k j = ∑ i', M i' j * ((starRingEnd ℂ) (u k i') * u k i) := by
          intro k
          rw [hFdef]
          simp only
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
        rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_comm]
        have hcomp : ∀ i' : Fin m, ∑ k, (starRingEnd ℂ) (u k i') * u k i
            = if i = i' then 1 else 0 := by
          intro i'
          have h := u.sum_repr' (EuclideanSpace.single i' (1 : ℂ))
          have h2 := congrArg (fun w : EuclideanSpace ℂ (Fin m) => w i) h
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, EuclideanSpace.single_apply] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          simp [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.single_apply]
        rw [Finset.sum_congr rfl fun i' _ => by rw [← Finset.mul_sum, hcomp i']]
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl, mul_one]; rfl
        · intro i' _ hi'; rw [if_neg (Ne.symm hi'), mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [h1, h2, h3]
  exact ⟨_, _, _, _, key.reindex (Fintype.equivFin _).symm⟩

/-- **Uniqueness** of the Schmidt coefficients. -/
theorem schmidt_coeff_unique (psi : Fin m → Fin n → ℂ) {r r' : ℕ}
    {s : Fin r → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {s' : Fin r' → ℝ} {e' : Fin r' → EuclideanSpace ℂ (Fin m)}
    {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (H : IsSchmidtDecomp psi s e f) (H' : IsSchmidtDecomp psi s' e' f') :
    (univ : Finset (Fin r)).val.map s = (univ : Finset (Fin r')).val.map s' := by
  classical
  have hop : specOp (fun k => (s k) ^ 2) e = specOp (fun k => (s' k) ^ 2) e' := by
    refine LinearMap.ext fun v => ?_
    ext i
    rw [H.specOp_apply_eq v i, H'.specOp_apply_eq v i]
  have hm := multiset_map_eq_of_specOp_eq (fun k => (s k) ^ 2) e (fun k => (s' k) ^ 2) e'
    H.orthonormal_left H'.orthonormal_left (fun k => pow_pos (H.coeff_pos k) 2)
    (fun k => pow_pos (H'.coeff_pos k) 2) hop
  have h2 := congrArg (Multiset.map Real.sqrt) hm
  rw [Multiset.map_map, Multiset.map_map] at h2
  have e1 : (Real.sqrt ∘ fun k => (s k) ^ 2) = s :=
    funext fun k => Real.sqrt_sq (le_of_lt (H.coeff_pos k))
  have e2 : (Real.sqrt ∘ fun k => (s' k) ^ 2) = s' :=
    funext fun k => Real.sqrt_sq (le_of_lt (H'.coeff_pos k))
  rwa [e1, e2] at h2

/-- **Schmidt decomposition.**  Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` admits a Schmidt
decomposition `psi = ∑ k, s k • (e k ⊗ f k)` with strictly positive coefficients `s k` and
orthonormal families `e`, `f`; moreover the Schmidt coefficients are unique as a multiset
(in particular their number, the Schmidt rank, is uniquely determined). -/
theorem schmidt_decomposition (psi : Fin m → Fin n → ℂ) :
    (∃ (r : ℕ) (s : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
        (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp psi s e f) ∧
      (∀ (r r' : ℕ) (s : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
          (f : Fin r → EuclideanSpace ℂ (Fin n)) (s' : Fin r' → ℝ)
          (e' : Fin r' → EuclideanSpace ℂ (Fin m)) (f' : Fin r' → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomp psi s e f → IsSchmidtDecomp psi s' e' f' →
          (univ : Finset (Fin r)).val.map s = (univ : Finset (Fin r')).val.map s') :=
  ⟨exists_schmidt psi, fun _ _ _ _ _ _ _ _ H H' => schmidt_coeff_unique psi H H'⟩

end QI

