/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/
noncomputable def amp (ψ : EuclideanSpace ℂ (Fin m × Fin n)) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun p q => ψ (p, q)

/-- The (unnormalised) reduced density matrix `ρ = M Mᴴ` of a bipartite pure state on the
first tensor factor. -/
noncomputable def rho (ψ : EuclideanSpace ℂ (Fin m × Fin n)) : Matrix (Fin m) (Fin m) ℂ :=
  amp ψ * (amp ψ).conjTranspose

/-- `IsSchmidt ψ lam e f` says that `lam`, `e`, `f` form a Schmidt decomposition of the
bipartite state `ψ`: the `lam i` are strictly positive reals (the Schmidt coefficients),
`e` and `f` are orthonormal families in the two factors, and
`ψ = ∑ i, lam i • (e i ⊗ f i)` in coordinates. -/
def IsSchmidt {r : ℕ} (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (lam : Fin r → ℝ)
    (e : Fin r → EuclideanSpace ℂ (Fin m)) (f : Fin r → EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ i, 0 < lam i) ∧ Orthonormal ℂ e ∧ Orthonormal ℂ f ∧
    ∀ p : Fin m × Fin n, ψ p = ∑ i, (lam i : ℂ) * e i p.1 * f i p.2

/-- The `s²`-eigenspace of the reduced density matrix of `ψ`. -/
noncomputable def eigsp (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (s : ℝ) : Submodule ℂ (Fin m → ℂ) :=
  LinearMap.ker ((rho ψ).mulVecLin - ((s : ℂ) ^ 2) • LinearMap.id)

/-! ### Basic coordinate lemmas -/

lemma inner_coord {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    inner ℂ x y = ∑ p, conj (x p) * y p := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

lemma orthonormal_iff_coord {r : ℕ} {ι : Type*} [Fintype ι] (e : Fin r → EuclideanSpace ℂ ι) :
    Orthonormal ℂ e ↔ ∀ i j, ∑ p, conj (e i p) * e j p = if i = j then (1 : ℂ) else 0 := by
  rw [orthonormal_iff_ite (𝕜 := ℂ)]
  constructor
  · intro h i j; rw [← inner_coord]; exact h i j
  · intro h i j; rw [inner_coord]; exact h i j

lemma rho_apply (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (p p' : Fin m) :
    rho ψ p p' = ∑ q, ψ (p, q) * conj (ψ (p', q)) := by
  simp [rho, amp, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma rho_isHermitian (ψ : EuclideanSpace ℂ (Fin m × Fin n)) : (rho ψ).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

lemma mem_eigsp_iff (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (s : ℝ) (v : Fin m → ℂ) :
    v ∈ eigsp ψ s ↔ ∀ p, ∑ p', rho ψ p p' * v p' = (s : ℂ) ^ 2 * v p := by
  simp only [eigsp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_zero, funext_iff, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul]

/-! ### Uniqueness -/

lemma linearIndependent_of_coordOrtho {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin m → ℂ))
    (h : ∀ i j, ∑ p, conj (v i p) * v j p = if i = j then (1 : ℂ) else 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h2 := congrArg (fun w : Fin m → ℂ => ∑ p, conj (v j p) * w p) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero] at h2
  have h3 : ∑ p, conj (v j p) * (∑ i, g i * v i p) = ∑ i, g i * ∑ p, conj (v j p) * v i p := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
  rw [h3] at h2
  simp only [h j] at h2
  simpa using h2

lemma rho_eq_of_schmidt {r : ℕ} {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (hd : IsSchmidt ψ lam e f) (p p' : Fin m) :
    rho ψ p p' = ∑ i, ((lam i : ℂ) ^ 2) * e i p * conj (e i p') := by
  obtain ⟨-, -, hfo, hpsi⟩ := hd
  rw [orthonormal_iff_coord] at hfo
  rw [rho_apply]
  have hf' : ∀ i j, ∑ q, f i q * conj (f j q) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    have h := congrArg (starRingEnd ℂ) (hfo i j)
    rw [map_sum] at h
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at h
    rw [h]
    split_ifs <;> simp
  have expand : ∀ q, ψ (p, q) * conj (ψ (p', q))
      = ∑ i, ∑ j, (((lam i : ℂ) * lam j) * (e i p * conj (e j p'))) * (f i q * conj (f j q)) := by
    intro q
    rw [hpsi (p, q), hpsi (p', q), map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ q, (((lam i : ℂ) * lam j) * (e i p * conj (e j p'))) * (f i q * conj (f j q))
      = (((lam i : ℂ) * lam j) * (e i p * conj (e j p'))) * (if i = j then (1 : ℂ) else 0) := by
    intro j; rw [← hf' i j, Finset.mul_sum]
  simp_rw [key]
  simp [Finset.sum_ite_eq]
  ring

lemma eigsp_eq_span {r : ℕ} {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (hd : IsSchmidt ψ lam e f) {s : ℝ} (hs : 0 < s) :
    eigsp ψ s = Submodule.span ℂ (Set.range fun i : {i : Fin r // lam i = s} =>
      ((e i : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)) := by
  obtain ⟨hpos, heo, hfo, hpsi⟩ := hd
  have he := (orthonormal_iff_coord e).mp heo
  have hs2 : ((s : ℂ)) ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 (by exact_mod_cast hs.ne' : (s : ℂ) ≠ 0)
  have key : ∀ (v : Fin m → ℂ) (p : Fin m), ∑ p', rho ψ p p' * v p'
      = ∑ i, ((lam i : ℂ) ^ 2) * (∑ p', conj (e i p') * v p') * e i p := by
    intro v p
    have hstep : ∀ p', rho ψ p p' * v p'
        = ∑ i, (((lam i : ℂ) ^ 2) * e i p * conj (e i p')) * v p' := by
      intro p'
      rw [rho_eq_of_schmidt ⟨hpos, heo, hfo, hpsi⟩ p p', Finset.sum_mul]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ p', (((lam i : ℂ) ^ 2) * e i p * conj (e i p')) * v p'
        = (((lam i : ℂ) ^ 2) * e i p) * (conj (e i p') * v p') := fun p' => by ring
    simp_rw [this]
    rw [← Finset.mul_sum]
    ring
  apply le_antisymm
  · intro v hv
    rw [mem_eigsp_iff] at hv
    set c : Fin r → ℂ := fun i => ∑ p', conj (e i p') * v p' with hcdef
    have hveq : ∀ p, ((s : ℂ)) ^ 2 * v p = ∑ i, ((lam i : ℂ) ^ 2) * c i * e i p := fun p => by
      rw [← hv p, key v p]
    have hcj : ∀ j, ((s : ℂ)) ^ 2 * c j = ((lam j : ℂ) ^ 2) * c j := by
      intro j
      have h1 : ∑ p, conj (e j p) * (((s : ℂ)) ^ 2 * v p)
          = ∑ p, conj (e j p) * (∑ i, ((lam i : ℂ) ^ 2) * c i * e i p) :=
        Finset.sum_congr rfl fun p _ => by rw [hveq p]
      have h2 : ∑ p, conj (e j p) * (((s : ℂ)) ^ 2 * v p) = ((s : ℂ)) ^ 2 * c j := by
        rw [hcdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
      have h3 : ∑ p, conj (e j p) * (∑ i, ((lam i : ℂ) ^ 2) * c i * e i p)
          = ((lam j : ℂ) ^ 2) * c j := by
        have hswap : ∑ p, conj (e j p) * (∑ i, ((lam i : ℂ) ^ 2) * c i * e i p)
            = ∑ i, ((lam i : ℂ) ^ 2) * c i * ∑ p, conj (e j p) * e i p := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
        rw [hswap]
        simp_rw [he j]
        simp
      rw [h2, h3] at h1
      exact h1
    have hcz : ∀ j, lam j ≠ s → c j = 0 := by
      intro j hj
      have hne : ((lam j : ℂ) ^ 2) - ((s : ℂ)) ^ 2 ≠ 0 := by
        have hreal : (lam j) ^ 2 - s ^ 2 ≠ 0 := by
          have h1 : lam j + s > 0 := by have := hpos j; linarith
          have h2 : lam j - s ≠ 0 := sub_ne_zero.mpr hj
          intro hcon
          have : (lam j - s) * (lam j + s) = 0 := by nlinarith [hcon]
          rcases mul_eq_zero.mp this with h | h
          · exact h2 h
          · linarith
        have : ((lam j : ℂ) ^ 2 - (s : ℂ) ^ 2) = (((lam j) ^ 2 - s ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this]
        exact_mod_cast hreal
      have := hcj j
      have : (((lam j : ℂ) ^ 2) - ((s : ℂ)) ^ 2) * c j = 0 := by linear_combination -this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · exact h
    have hsum : v = ∑ i : {i : Fin r // lam i = s}, c i •
        ((e i : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ) := by
      funext p
      have hstep : ∑ i, ((lam i : ℂ) ^ 2) * c i * e i p
          = ((s : ℂ)) ^ 2 * ∑ i, (if lam i = s then c i * e i p else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : lam i = s
        · rw [if_pos h, h]; ring
        · rw [if_neg h, hcz i h]; ring
      have h4 : ((s : ℂ)) ^ 2 * v p
          = ((s : ℂ)) ^ 2 * ∑ i, (if lam i = s then c i * e i p else 0) := by
        rw [hveq p, hstep]
      have h5 : v p = ∑ i, (if lam i = s then c i * e i p else 0) :=
        mul_left_cancel₀ hs2 h4
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h5, ← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter fun i => lam i = s)
        (fun x => by simp) (fun i => c i * e i p)
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_eigsp_iff]
    intro p
    rw [key]
    have : ∀ i, ((lam i : ℂ) ^ 2) * (∑ p', conj (e i p') * e j p') * e i p
        = ((lam i : ℂ) ^ 2) * (if i = j then (1 : ℂ) else 0) * e i p := by
      intro i; rw [he i j]
    simp_rw [this]
    simp [Finset.sum_ite_eq', j.2]

lemma finrank_eigsp {r : ℕ} {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (hd : IsSchmidt ψ lam e f) {s : ℝ} (hs : 0 < s) :
    Module.finrank ℂ (eigsp ψ s) = (Finset.univ.filter fun i => lam i = s).card := by
  have he := (orthonormal_iff_coord e).mp hd.2.1
  have hli : LinearIndependent ℂ (fun i : {i : Fin r // lam i = s} =>
      ((e i : EuclideanSpace ℂ (Fin m)) : Fin m → ℂ)) := by
    refine linearIndependent_of_coordOrtho _ fun i j => ?_
    rw [he i j]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]
  rw [eigsp_eq_span hd hs, finrank_span_eq_card hli, Fintype.card_subtype]

/-! ### Existence -/

/-- An orthonormal eigenbasis of the reduced density matrix of `ψ`. -/
noncomputable def evecs (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) :=
  (rho_isHermitian ψ).eigenvectorBasis

/-- The corresponding eigenvalues of the reduced density matrix of `ψ`. -/
noncomputable def evals (ψ : EuclideanSpace ℂ (Fin m × Fin n)) : Fin m → ℝ :=
  (rho_isHermitian ψ).eigenvalues

/-- The (unnormalised) partner vectors in the second factor. -/
noncomputable def wcoef (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j : Fin m) (q : Fin n) : ℂ :=
  ∑ p, conj (evecs ψ j p) * ψ (p, q)

lemma evecs_ortho (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j k : Fin m) :
    ∑ p, conj (evecs ψ j p) * evecs ψ k p = if j = k then (1 : ℂ) else 0 :=
  (orthonormal_iff_coord (fun j => evecs ψ j)).mp (evecs ψ).orthonormal j k

lemma rho_mulVec_evecs (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j : Fin m) (p : Fin m) :
    ∑ p', rho ψ p p' * evecs ψ j p' = (evals ψ j : ℂ) * evecs ψ j p := by
  have h := congrFun ((rho_isHermitian ψ).mulVec_eigenvectorBasis j) p
  simpa [evecs, evals, Matrix.mulVec, dotProduct, RCLike.real_smul_eq_coe_smul (K := ℂ)] using h

lemma psi_eq_sum_evecs (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (p : Fin m) (q : Fin n) :
    ψ (p, q) = ∑ j, evecs ψ j p * wcoef ψ j q := by
  set b := evecs ψ with hb
  set x : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun p => ψ (p, q)) with hx
  have h := congrArg (fun y : EuclideanSpace ℂ (Fin m) => y p) (b.sum_repr' x)
  simp only at h
  have hxp : x p = ψ (p, q) := rfl
  rw [← hxp, ← h, WithLp.ofLp_sum]
  simp only [Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, hx, wcoef, hb]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun p' _ => mul_comm _ _

lemma wcoef_inner (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j k : Fin m) :
    ∑ q, conj (wcoef ψ j q) * wcoef ψ k q = if j = k then (evals ψ j : ℂ) else 0 := by
  simp only [wcoef]
  have step1 : ∀ q, conj (∑ p, conj (evecs ψ j p) * ψ (p, q))
        * (∑ p, conj (evecs ψ k p) * ψ (p, q))
      = ∑ p, ∑ p', (evecs ψ j p * conj (evecs ψ k p')) * (ψ (p', q) * conj (ψ (p, q))) := by
    intro q
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  simp_rw [step1]
  rw [Finset.sum_comm]
  have swap2 : ∀ p, ∑ q, ∑ p', (evecs ψ j p * conj (evecs ψ k p')) * (ψ (p', q) * conj (ψ (p, q)))
      = ∑ p', (evecs ψ j p * conj (evecs ψ k p')) * rho ψ p' p := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [rho_apply, Finset.mul_sum]
  simp_rw [swap2]
  rw [Finset.sum_comm]
  have inner1 : ∀ p', ∑ p, (evecs ψ j p * conj (evecs ψ k p')) * rho ψ p' p
      = conj (evecs ψ k p') * ((evals ψ j : ℂ) * evecs ψ j p') := by
    intro p'
    rw [← rho_mulVec_evecs ψ j p', Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  simp_rw [inner1]
  have hlast : ∑ p', conj (evecs ψ k p') * ((evals ψ j : ℂ) * evecs ψ j p')
      = (evals ψ j : ℂ) * ∑ p', conj (evecs ψ k p') * evecs ψ j p' := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p' _ => by ring
  rw [hlast, evecs_ortho ψ k j]
  by_cases h : j = k
  · simp [h]
  · simp [h, Ne.symm h]

lemma evals_eq_sum_normSq (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j : Fin m) :
    evals ψ j = ∑ q, Complex.normSq (wcoef ψ j q) := by
  have h := wcoef_inner ψ j j
  rw [if_pos rfl] at h
  have h2 : ((∑ q, Complex.normSq (wcoef ψ j q) : ℝ) : ℂ) = (evals ψ j : ℂ) := by
    rw [← h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [Complex.normSq_eq_conj_mul_self]
  exact_mod_cast h2.symm

lemma evals_nonneg (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (j : Fin m) : 0 ≤ evals ψ j := by
  rw [evals_eq_sum_normSq]
  exact Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _

lemma wcoef_eq_zero (ψ : EuclideanSpace ℂ (Fin m × Fin n)) {j : Fin m} (hj : evals ψ j = 0)
    (q : Fin n) : wcoef ψ j q = 0 := by
  rw [evals_eq_sum_normSq] at hj
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q _ => Complex.normSq_nonneg (wcoef ψ j q))).mp hj q (Finset.mem_univ q)
  exact Complex.normSq_eq_zero.mp this

lemma sum_evals (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (hψ : ‖ψ‖ = 1) :
    ∑ j, evals ψ j = 1 := by
  have htr : (rho ψ).trace = ∑ j, (evals ψ j : ℂ) :=
    (rho_isHermitian ψ).trace_eq_sum_eigenvalues
  have hinner : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have htr2 : (rho ψ).trace = (inner ℂ ψ ψ : ℂ) := by
    rw [Matrix.trace]
    rw [inner_coord, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.diag_apply, rho_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [mul_comm]
  rw [htr2, hinner] at htr
  exact_mod_cast htr.symm

lemma exists_schmidt (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (hψ : ‖ψ‖ = 1) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidt ψ lam e f ∧ ∑ i, lam i ^ 2 = 1 := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun j => evals ψ j ≠ 0) with hS
  set g : Fin S.card → Fin m := fun t => ((S.equivFin.symm t : {x // x ∈ S}) : Fin m) with hg
  have hgmem : ∀ t, g t ∈ S := fun t => (S.equivFin.symm t).2
  have hginj : Function.Injective g := by
    intro t u h
    exact S.equivFin.symm.injective (Subtype.ext h)
  have hposv : ∀ t, 0 < evals ψ (g t) := by
    intro t
    have hne : evals ψ (g t) ≠ 0 := by
      have := hgmem t
      rw [hS, Finset.mem_filter] at this
      exact this.2
    exact lt_of_le_of_ne (evals_nonneg ψ _) (Ne.symm hne)
  have hsqpos : ∀ t, 0 < Real.sqrt (evals ψ (g t)) := fun t => Real.sqrt_pos.mpr (hposv t)
  have hsq : ∀ t, (Real.sqrt (evals ψ (g t))) ^ 2 = evals ψ (g t) := fun t =>
    Real.sq_sqrt (evals_nonneg ψ _)
  have hreindexC : ∀ F : Fin m → ℂ, ∑ t, F (g t) = ∑ j ∈ S, F j := by
    intro F
    rw [hg]
    rw [Equiv.sum_comp S.equivFin.symm (fun x : {x // x ∈ S} => F x)]
    exact Finset.sum_coe_sort S F
  have hreindexR : ∀ F : Fin m → ℝ, ∑ t, F (g t) = ∑ j ∈ S, F j := by
    intro F
    rw [hg]
    rw [Equiv.sum_comp S.equivFin.symm (fun x : {x // x ∈ S} => F x)]
    exact Finset.sum_coe_sort S F
  refine ⟨S.card, fun t => Real.sqrt (evals ψ (g t)), fun t => evecs ψ (g t),
    fun t => WithLp.toLp 2 (fun q => (1 / (Real.sqrt (evals ψ (g t)) : ℂ)) * wcoef ψ (g t) q),
    ⟨hsqpos, ?_, ?_, ?_⟩, ?_⟩
  · exact (evecs ψ).orthonormal.comp g hginj
  · rw [orthonormal_iff_coord]
    intro t u
    have hconj : ∀ t' : Fin S.card, conj ((1 : ℂ) / (Real.sqrt (evals ψ (g t')) : ℂ))
        = 1 / (Real.sqrt (evals ψ (g t')) : ℂ) := by
      intro t'
      simp [Complex.conj_ofReal]
    have hstep : ∀ q, conj ((WithLp.toLp 2 (fun q => (1 / (Real.sqrt (evals ψ (g t)) : ℂ))
            * wcoef ψ (g t) q) : EuclideanSpace ℂ (Fin n)) q)
          * ((WithLp.toLp 2 (fun q => (1 / (Real.sqrt (evals ψ (g u)) : ℂ))
            * wcoef ψ (g u) q) : EuclideanSpace ℂ (Fin n)) q)
        = ((1 / (Real.sqrt (evals ψ (g t)) : ℂ)) * (1 / (Real.sqrt (evals ψ (g u)) : ℂ)))
            * (conj (wcoef ψ (g t) q) * wcoef ψ (g u) q) := by
      intro q
      simp only [map_mul, hconj]
      ring
    simp_rw [hstep]
    rw [← Finset.mul_sum, wcoef_inner]
    by_cases h : t = u
    · subst h
      rw [if_pos rfl, if_pos rfl]
      have h1 : (Real.sqrt (evals ψ (g t)) : ℂ) ≠ 0 := by
        exact_mod_cast (hsqpos t).ne'
      field_simp
      rw [← Complex.ofReal_pow, hsq t]
    · rw [if_neg h, if_neg (fun hc => h (hginj hc)), mul_zero]
  · intro p
    have hRHS : ∀ t : Fin S.card, ((Real.sqrt (evals ψ (g t)) : ℂ)) * evecs ψ (g t) p.1
          * ((WithLp.toLp 2 (fun q => (1 / (Real.sqrt (evals ψ (g t)) : ℂ))
              * wcoef ψ (g t) q) : EuclideanSpace ℂ (Fin n)) p.2)
        = evecs ψ (g t) p.1 * wcoef ψ (g t) p.2 := by
      intro t
      have h1 : (Real.sqrt (evals ψ (g t)) : ℂ) ≠ 0 := by
        exact_mod_cast (hsqpos t).ne'
      field_simp
    simp_rw [hRHS]
    rw [hreindexC (fun j => evecs ψ j p.1 * wcoef ψ j p.2)]
    have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)) \ S,
        evecs ψ j p.1 * wcoef ψ j p.2 = 0 := by
      intro j hj
      rw [Finset.mem_sdiff, hS, Finset.mem_filter] at hj
      have : evals ψ j = 0 := by
        by_contra hc
        exact hj.2 ⟨Finset.mem_univ j, hc⟩
      rw [wcoef_eq_zero ψ this, mul_zero]
    rw [Finset.sum_subset (Finset.subset_univ S)
      (fun j hju hj => hzero j (Finset.mem_sdiff.mpr ⟨hju, hj⟩))]
    exact psi_eq_sum_evecs ψ p.1 p.2
  · simp_rw [hsq]
    rw [hreindexR (fun j => evals ψ j)]
    rw [Finset.sum_subset (Finset.subset_univ S) (fun j hju hj => ?_)]
    · exact sum_evals ψ hψ
    · by_contra hc
      rw [hS, Finset.mem_filter] at hj
      exact hj ⟨hju, hc⟩

/-! ### Main theorem -/

/-- **Schmidt decomposition.** Every bipartite pure state `ψ` (a unit vector of the tensor
product, presented via its amplitudes in the product basis) admits a Schmidt decomposition
`ψ = ∑ i, lam i • (e i ⊗ f i)` with strictly positive Schmidt coefficients `lam i` summing
(in squares) to one, and orthonormal families `e`, `f`; moreover the Schmidt coefficients are
unique: any two Schmidt decompositions of `ψ` have the same number of terms and the same
multiset of coefficients. -/
theorem schmidt_decomposition {m n : ℕ} (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (hψ : ‖ψ‖ = 1) :
    (∃ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
        (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidt ψ lam e f ∧ ∑ i, lam i ^ 2 = 1) ∧
    (∀ (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
        (f : Fin r → EuclideanSpace ℂ (Fin n)) (r' : ℕ) (lam' : Fin r' → ℝ)
        (e' : Fin r' → EuclideanSpace ℂ (Fin m)) (f' : Fin r' → EuclideanSpace ℂ (Fin n)),
      IsSchmidt ψ lam e f → IsSchmidt ψ lam' e' f' →
        r = r' ∧ Multiset.map lam Finset.univ.val = Multiset.map lam' Finset.univ.val) := by
  refine ⟨exists_schmidt ψ hψ, ?_⟩
  intro r lam e f r' lam' e' f' hd hd'
  have hcard : ∀ s : ℝ, (Finset.univ.filter fun i => lam i = s).card
      = (Finset.univ.filter fun i => lam' i = s).card := by
    intro s
    rcases lt_or_ge 0 s with hs | hs
    · rw [← finrank_eigsp hd hs, ← finrank_eigsp hd' hs]
    · have h1 : (Finset.univ.filter fun i => lam i = s) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun {i} _ hc => absurd (hc ▸ hd.1 i) (by linarith)
      have h2 : (Finset.univ.filter fun i => lam' i = s) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun {i} _ hc => absurd (hc ▸ hd'.1 i) (by linarith)
      rw [h1, h2]
      simp
  have hmul : Multiset.map lam Finset.univ.val = Multiset.map lam' Finset.univ.val := by
    ext s
    rw [Multiset.count_map, Multiset.count_map]
    have e1 : (Multiset.filter (fun a => s = lam a) (Finset.univ.val : Multiset (Fin r))).card
        = (Finset.univ.filter fun i => lam i = s).card := by
      simp [Finset.card, Finset.filter, eq_comm]
    have e2 : (Multiset.filter (fun a => s = lam' a) (Finset.univ.val : Multiset (Fin r'))).card
        = (Finset.univ.filter fun i => lam' i = s).card := by
      simp [Finset.card, Finset.filter, eq_comm]
    rw [e1, e2, hcard s]
  refine ⟨?_, hmul⟩
  have := congrArg Multiset.card hmul
  simpa using this

end QI

