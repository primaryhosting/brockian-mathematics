/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/
def IsOrthonormalFamily {ι : Type*} [DecidableEq ι] (u : ι → A → ℂ) : Prop :=
  ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0

/-- `(s, u, v)` is a Schmidt decomposition of the bipartite pure state with amplitudes
`psi i j` (the amplitude of the product basis vector `|i⟩ ⊗ |j⟩`):  the Schmidt
coefficients `s k` are positive reals, the families `u` and `v` are orthonormal in the two
factors, and `psi i j = ∑ k, s k * u k i * v k j`. -/
def IsSchmidtDecomposition {r : ℕ} (psi : A → B → ℂ) (s : Fin r → ℝ)
    (u : Fin r → A → ℂ) (v : Fin r → B → ℂ) : Prop :=
  (∀ k, 0 < s k) ∧ IsOrthonormalFamily u ∧ IsOrthonormalFamily v ∧
    ∀ i j, psi i j = ∑ k, (s k : ℂ) * u k i * v k j

/-- The (unnormalised) reduced density matrix of the first factor. -/
noncomputable def reduced (psi : A → B → ℂ) : Matrix A A ℂ :=
  fun i i' => ∑ j, psi i j * conj (psi i' j)

omit [DecidableEq B] in
theorem IsOrthonormalFamily.conj_right {ι : Type*} [DecidableEq ι] {v : ι → B → ℂ}
    (h : IsOrthonormalFamily v) (k l : ι) :
    ∑ b, v k b * conj (v l b) = if k = l then 1 else 0 := by
  have := h l k
  rw [show (if l = k then (1 : ℂ) else 0) = (if k = l then (1 : ℂ) else 0) by
    simp [eq_comm]] at this
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-! ### Existence -/

/-- The spectral data of the Gram matrix `psiᴴ psi`: an orthonormal, complete family of
eigenvectors `w` with real eigenvalues `μ`. -/
theorem exists_eigen_data (psi : A → B → ℂ) :
    ∃ (w : B → B → ℂ) (mu : B → ℝ),
      (∀ k l, ∑ b, conj (w k b) * w l b = if k = l then 1 else 0) ∧
      (∀ a b, ∑ j, w j a * conj (w j b) = if a = b then 1 else 0) ∧
      (∀ j a, ∑ b, (∑ i, conj (psi i a) * psi i b) * w j b = (mu j : ℂ) * w j a) := by
  set G : Matrix B B ℂ := Matrix.of (fun a b => ∑ i, conj (psi i a) * psi i b) with hG
  have hherm : G.IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, hG, Matrix.of_apply, star_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  refine ⟨fun j => (hherm.eigenvectorBasis j).ofLp, hherm.eigenvalues, ?_, ?_, ?_⟩
  · intro k l
    have hmem := hherm.eigenvectorUnitary.2
    rw [Unitary.mem_iff] at hmem
    have := congrFun (congrFun hmem.1 k) l
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using this
  · intro a b
    have hmem := hherm.eigenvectorUnitary.2
    rw [Unitary.mem_iff] at hmem
    have := congrFun (congrFun hmem.2 a) b
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using this
  · intro j a
    have := congrFun (hherm.mulVec_eigenvectorBasis j) a
    simpa [Matrix.mulVec, dotProduct, hG, Complex.real_smul] using this

theorem sum_mul_sum_expand {I J : Type*} [Fintype I] [Fintype J] (F : I → ℂ) (G : J → ℂ) :
    (∑ a, F a) * (∑ b, G b) = ∑ a, ∑ b, F a * G b := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _

theorem sum3_comm {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] (f : I → J → K → ℂ) :
    ∑ i, ∑ a, ∑ b, f i a b = ∑ a, ∑ b, ∑ i, f i a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem exists_schmidt (psi : A → B → ℂ) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → A → ℂ) (v : Fin r → B → ℂ),
      IsSchmidtDecomposition psi s u v := by
  classical
  obtain ⟨w, mu, hw1, hw2, hw3⟩ := exists_eigen_data psi
  set y : B → A → ℂ := fun j i => ∑ b, psi i b * w j b with hy
  -- the vectors `y j = psi *ᵥ w j` are orthogonal with squared norms the eigenvalues
  have hyy : ∀ k l, ∑ i, conj (y k i) * y l i = (mu l : ℂ) * (if k = l then 1 else 0) := by
    intro k l
    have e0 : ∀ i, conj (y k i) * y l i
        = ∑ a, ∑ b, (conj (psi i a) * conj (w k a)) * (psi i b * w l b) := by
      intro i
      show (conj (∑ b, psi i b * w k b)) * (∑ b, psi i b * w l b) = _
      rw [map_sum]
      simp only [map_mul]
      exact sum_mul_sum_expand _ _
    calc ∑ i, conj (y k i) * y l i
        = ∑ i, ∑ a, ∑ b, (conj (psi i a) * conj (w k a)) * (psi i b * w l b) :=
          Finset.sum_congr rfl fun i _ => e0 i
      _ = ∑ a, ∑ b, ∑ i, (conj (psi i a) * conj (w k a)) * (psi i b * w l b) := sum3_comm _
      _ = ∑ a, conj (w k a) * ((mu l : ℂ) * w l a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← hw3 l a, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (mu l : ℂ) * (if k = l then 1 else 0) := by
          rw [← hw1 k l, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
  have hnorm : ∀ j, mu j = ∑ i, Complex.normSq (y j i) := by
    intro j
    have h1 : ∑ i, conj (y j i) * y j i = ((mu j : ℝ) : ℂ) := by simpa using hyy j j
    have h2 : ((mu j : ℝ) : ℂ) = ((∑ i, Complex.normSq (y j i) : ℝ) : ℂ) := by
      rw [← h1, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_conj_mul_self).symm
    exact_mod_cast h2
  have hmu : ∀ j, 0 ≤ mu j := by
    intro j
    rw [hnorm j]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hy0 : ∀ j, mu j = 0 → ∀ i, y j i = 0 := by
    intro j hj i
    have h2 : ∑ i, Complex.normSq (y j i) = 0 := by rw [← hnorm j, hj]
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg (y j i))).mp h2 i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp this
  have hrec0 : ∀ i b, psi i b = ∑ j, y j i * conj (w j b) := by
    intro i b
    have e1 : ∑ j, y j i * conj (w j b) = ∑ a, psi i a * (∑ j, w j a * conj (w j b)) := by
      simp only [hy, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]
    simp [hw2]
  -- the Schmidt data, indexed by the positive eigenvalues
  set S := {j : B // 0 < mu j} with hS
  set e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S with he
  have hinj : ∀ k l : Fin (Fintype.card S),
      ((e.symm k : S) : B) = ((e.symm l : S) : B) ↔ k = l := by
    intro k l
    constructor
    · intro hh
      have : e.symm k = e.symm l := Subtype.ext hh
      simpa using congrArg e this
    · rintro rfl; rfl
  have hposk : ∀ k : Fin (Fintype.card S), 0 < Real.sqrt (mu ((e.symm k : S) : B)) :=
    fun k => Real.sqrt_pos.mpr (e.symm k).2
  refine ⟨Fintype.card S, fun k => Real.sqrt (mu ((e.symm k : S) : B)),
    fun k i => ((Real.sqrt (mu ((e.symm k : S) : B)))⁻¹ : ℝ) * y ((e.symm k : S) : B) i,
    fun k b => conj (w ((e.symm k : S) : B) b), hposk, ?_, ?_, ?_⟩
  · -- orthonormality of the `u`'s
    intro k l
    have hstep : ∀ (c d : ℝ) (j j' : B),
        ∑ i, conj ((c : ℂ) * y j i) * ((d : ℂ) * y j' i)
          = (c : ℂ) * (d : ℂ) * ((mu j' : ℂ) * (if j = j' then 1 else 0)) := by
      intro c d j j'
      rw [← hyy j j', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, Complex.conj_ofReal]
      ring
    rw [hstep _ _ _ _]
    by_cases hkl : k = l
    · subst hkl
      have hp := hposk k
      rw [if_pos rfl, if_pos rfl, mul_one]
      have hreal : (Real.sqrt (mu ((e.symm k : S) : B)))⁻¹
          * (Real.sqrt (mu ((e.symm k : S) : B)))⁻¹ * mu ((e.symm k : S) : B) = 1 := by
        have hsq : Real.sqrt (mu ((e.symm k : S) : B)) * Real.sqrt (mu ((e.symm k : S) : B))
            = mu ((e.symm k : S) : B) := Real.mul_self_sqrt (hmu _)
        have hne : Real.sqrt (mu ((e.symm k : S) : B)) ≠ 0 := (hposk k).ne'
        field_simp
        linarith [hsq]
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hreal
    · rw [if_neg hkl, if_neg (fun hcon => hkl ((hinj k l).mp hcon))]
      ring
  · -- orthonormality of the `v`'s
    intro k l
    have e2 : ∑ b, conj (conj (w ((e.symm k : S) : B) b)) * conj (w ((e.symm l : S) : B) b)
        = conj (∑ b, conj (w ((e.symm k : S) : B) b) * w ((e.symm l : S) : B) b) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun b _ => by simp
    rw [e2, hw1]
    by_cases hkl : k = l
    · subst hkl; simp
    · rw [if_neg (fun hcon => hkl ((hinj k l).mp hcon)), if_neg hkl, map_zero]
  · -- reconstruction
    intro i b
    have hsum : ∀ k : Fin (Fintype.card S),
        ((Real.sqrt (mu ((e.symm k : S) : B)) : ℝ) : ℂ)
            * (((Real.sqrt (mu ((e.symm k : S) : B)))⁻¹ : ℝ) * y ((e.symm k : S) : B) i)
            * conj (w ((e.symm k : S) : B) b)
          = y ((e.symm k : S) : B) i * conj (w ((e.symm k : S) : B) b) := by
      intro k
      have hp := (hposk k).ne'
      have : ((Real.sqrt (mu ((e.symm k : S) : B)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hp
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hsum k]
    rw [Equiv.sum_comp e.symm (fun j : S => y (j : B) i * conj (w (j : B) b))]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun j => 0 < mu j)) (by simp)
      (fun j => y j i * conj (w j b))]
    rw [hrec0 i b]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    rw [hy0 j (le_antisymm hj (hmu j)) i, zero_mul]

/-! ### Uniqueness -/

/-- The eigenspace of a matrix, as a submodule of `A → ℂ`. -/
def eigSp (R : Matrix A A ℂ) (t : ℂ) : Submodule ℂ (A → ℂ) :=
  Module.End.eigenspace (Matrix.mulVecLin R) t

theorem mem_eigSp_iff {R : Matrix A A ℂ} {t : ℂ} {x : A → ℂ} :
    x ∈ eigSp R t ↔ ∀ i, ∑ i', R i i' * x i' = t * x i := by
  simp [eigSp, funext_iff, Matrix.mulVec, dotProduct]

omit [DecidableEq B] in
/-- Contraction of two expansions in an orthonormal family. -/
theorem sum_mul_conj_of_orthonormal {r : ℕ} {v : Fin r → B → ℂ} (hv : IsOrthonormalFamily v)
    (a d : Fin r → ℂ) :
    ∑ b, (∑ k, a k * v k b) * (∑ l, d l * conj (v l b)) = ∑ k, a k * d k := by
  have hv' := hv.conj_right
  have expand : ∀ b : B, (∑ k, a k * v k b) * (∑ l, d l * conj (v l b))
      = ∑ k, ∑ l, (a k * d l) * (v k b * conj (v l b)) := by
    intro b
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => expand b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hk : ∀ l : Fin r, (∑ b, (a k * d l) * (v k b * conj (v l b)))
      = (a k * d l) * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hv' k l]
  simp only [hk]
  simp

omit [DecidableEq B] in
/-- The reduced density matrix acts on `x` through the Schmidt vectors. -/
theorem reduced_apply {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) (x : A → ℂ) (i : A) :
    ∑ i', reduced psi i i' * x i' = ∑ k, ((s k : ℂ) ^ 2 * ∑ i', conj (u k i') * x i') * u k i := by
  obtain ⟨hs, hu, hv, hrec⟩ := h
  set c : Fin r → ℂ := fun l => ∑ i', conj (u l i') * x i' with hc
  have step1 : ∑ i', reduced psi i i' * x i'
      = ∑ b, psi i b * ∑ i', conj (psi i' b) * x i' := by
    simp only [reduced, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i' _ => by ring
  have step2 : ∀ b, ∑ i', conj (psi i' b) * x i'
      = ∑ l, ((s l : ℂ) * c l) * conj (v l b) := by
    intro b
    have : ∀ i' : A, conj (psi i' b) * x i'
        = ∑ l, ((s l : ℂ) * conj (v l b)) * (conj (u l i') * x i') := by
      intro i'
      rw [hrec i' b]
      simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    simp only [hc]
    ring
  have step3 : ∀ b, psi i b = ∑ k, ((s k : ℂ) * u k i) * v k b := by
    intro b
    rw [hrec i b]
  rw [step1]
  simp only [step2, step3]
  rw [sum_mul_conj_of_orthonormal hv (fun k => (s k : ℂ) * u k i) (fun l => (s l : ℂ) * c l)]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq B] in
/-- Each Schmidt vector `u l` is an eigenvector of the reduced density matrix with
eigenvalue `(s l)^2`. -/
theorem reduced_eigenvector {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) (l : Fin r) :
    u l ∈ eigSp (reduced psi) ((s l : ℂ) ^ 2) := by
  rw [mem_eigSp_iff]
  intro i
  have hu : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := h.2.1
  rw [reduced_apply h (u l) i]
  simp only [hu]
  simp

omit [DecidableEq B] in
theorem schmidt_linearIndependent {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) (t : ℝ) :
    LinearIndependent ℂ (fun k : {k : Fin r // s k = t} => u k.val) := by
  have hu : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := h.2.1
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have hg' : ∀ i, ∑ k : {k : Fin r // s k = t}, g k * u k.val i = 0 := by
    intro i
    have := congrFun hg i
    simpa using this
  have key : ∑ k : {k : Fin r // s k = t}, g k * (if (l : Fin r) = (k : Fin r) then (1 : ℂ) else 0)
      = 0 := by
    have e1 : ∀ i : A, conj (u l.val i) * (∑ k : {k : Fin r // s k = t}, g k * u k.val i)
        = ∑ k : {k : Fin r // s k = t}, g k * (conj (u l.val i) * u k.val i) := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ k : {k : Fin r // s k = t}, g k * (if (l : Fin r) = (k : Fin r) then (1 : ℂ) else 0)
        = ∑ k : {k : Fin r // s k = t}, g k * ∑ i, conj (u l.val i) * u k.val i := by
          exact Finset.sum_congr rfl fun k _ => by rw [hu l.val k.val]
      _ = ∑ i, conj (u l.val i) * (∑ k : {k : Fin r // s k = t}, g k * u k.val i) := by
          simp only [e1]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ = 0 := by simp [hg']
  simpa [← Subtype.ext_iff, Finset.sum_ite_eq] using key

omit [DecidableEq B] in
theorem span_schmidt_eq_eigSp {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) {t : ℝ} (ht : 0 < t) :
    Submodule.span ℂ (Set.range (fun k : {k : Fin r // s k = t} => u k.val))
      = eigSp (reduced psi) ((t : ℂ) ^ 2) := by
  have hs := h.1
  have hu : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := h.2.1
  have htne : ((t : ℂ)) ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨k, rfl⟩
    have := reduced_eigenvector h k.val
    rw [k.property] at this
    exact this
  · intro x hx
    rw [mem_eigSp_iff] at hx
    set c : Fin r → ℂ := fun k => ∑ i', conj (u k i') * x i' with hcdef
    have hxi : ∀ i, ((t : ℂ) ^ 2) * x i = ∑ k, ((s k : ℂ) ^ 2 * c k) * u k i := by
      intro i
      rw [← hx i, reduced_apply h x i]
    -- the coefficients `c l` vanish unless `s l = t`
    have hcl : ∀ l, ((t : ℂ) ^ 2) * c l = ((s l : ℂ) ^ 2) * c l := by
      intro l
      have e1 : ((t : ℂ) ^ 2) * c l = ∑ i, conj (u l i) * (((t : ℂ) ^ 2) * x i) := by
        rw [hcdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1]
      have e2 : ∀ i : A, conj (u l i) * (∑ k, ((s k : ℂ) ^ 2 * c k) * u k i)
          = ∑ k, ((s k : ℂ) ^ 2 * c k) * (conj (u l i) * u k i) := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      calc ∑ i, conj (u l i) * (((t : ℂ) ^ 2) * x i)
          = ∑ i, conj (u l i) * (∑ k, ((s k : ℂ) ^ 2 * c k) * u k i) := by
            exact Finset.sum_congr rfl fun i _ => by rw [hxi i]
        _ = ∑ k, ((s k : ℂ) ^ 2 * c k) * ∑ i, conj (u l i) * u k i := by
            simp only [e2]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
        _ = ((s l : ℂ) ^ 2) * c l := by
            simp only [hu]
            simp
    have hzero : ∀ l, s l ≠ t → c l = 0 := by
      intro l hl
      have h1 : (((t : ℂ) ^ 2) - ((s l : ℂ) ^ 2)) * c l = 0 := by
        have := hcl l; ring_nf; ring_nf at this; linear_combination this
      have h2 : (((t : ℂ) ^ 2) - ((s l : ℂ) ^ 2)) ≠ 0 := by
        have : (t : ℝ) ^ 2 - (s l) ^ 2 ≠ 0 := by
          have hpos := hs l
          intro hcon
          apply hl
          nlinarith [sq_nonneg (t - s l), sq_nonneg (t + s l)]
        intro hcon
        apply this
        have : ((((t : ℝ) ^ 2 - (s l) ^ 2 : ℝ)) : ℂ) = 0 := by push_cast; linear_combination hcon
        exact_mod_cast this
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hx_eq : ∀ i, x i = ∑ k : {k : Fin r // s k = t}, c k.val * u k.val i := by
      intro i
      have e3 : ∑ k, ((s k : ℂ) ^ 2 * c k) * u k i
          = ∑ k, ((t : ℂ) ^ 2) * ((if s k = t then c k else 0) * u k i) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : s k = t
        · simp [hk]; ring
        · simp [hk, hzero k hk]
      have e4 : ((t : ℂ) ^ 2) * x i
          = ((t : ℂ) ^ 2) * ∑ k, (if s k = t then c k else 0) * u k i := by
        rw [hxi i, e3, ← Finset.mul_sum]
      have e5 : x i = ∑ k, (if s k = t then c k else 0) * u k i :=
        mul_left_cancel₀ htne e4
      rw [e5]
      rw [← Finset.sum_subtype (Finset.univ.filter (fun k => s k = t))
        (by intro k; simp) (fun k => c k * u k i)]
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun k _ => by by_cases hk : s k = t <;> simp [hk]
    have : x = ∑ k : {k : Fin r // s k = t}, c k.val • u k.val := by
      funext i
      rw [hx_eq i]
      simp
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨k, rfl⟩

omit [DecidableEq B] in
theorem card_schmidt_eq_finrank {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) {t : ℝ} (ht : 0 < t) :
    Fintype.card {k : Fin r // s k = t}
      = Module.finrank ℂ (eigSp (reduced psi) ((t : ℂ) ^ 2)) := by
  rw [← span_schmidt_eq_eigSp h ht, finrank_span_eq_card (schmidt_linearIndependent h t)]

omit [DecidableEq B] in
theorem schmidt_unique {r r' : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} {s' : Fin r' → ℝ} {u' : Fin r' → A → ℂ} {v' : Fin r' → B → ℂ}
    (h : IsSchmidtDecomposition psi s u v) (h' : IsSchmidtDecomposition psi s' u' v') :
    Multiset.map s Finset.univ.val = Multiset.map s' Finset.univ.val := by
  refine Multiset.ext.mpr fun a => ?_
  rw [Multiset.count_map, Multiset.count_map]
  rcases lt_or_ge 0 a with ha | ha
  · have e : ∀ {n : ℕ} (f : Fin n → ℝ),
        (Multiset.filter (fun k => a = f k) (Finset.univ : Finset (Fin n)).val).card
          = Fintype.card {k : Fin n // f k = a} := by
      intro n f
      have hfil : Multiset.filter (fun k : Fin n => a = f k) (Finset.univ : Finset (Fin n)).val
          = Multiset.filter (fun k : Fin n => f k = a) (Finset.univ : Finset (Fin n)).val :=
        Multiset.filter_congr fun k _ => eq_comm
      rw [hfil, ← Finset.filter_val, Fintype.card_subtype]
      rfl
    rw [e s, e s', card_schmidt_eq_finrank h ha, card_schmidt_eq_finrank h' ha]
  · have e : ∀ {n : ℕ} (f : Fin n → ℝ), (∀ k, 0 < f k) →
        (Multiset.filter (fun k => a = f k) (Finset.univ : Finset (Fin n)).val).card = 0 := by
      intro n f hf
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro k _ hk
      exact absurd (hk ▸ hf k) (by simpa using ha)
    rw [e s h.1, e s' h'.1]

omit [DecidableEq B] in
/-- The sum of the squares of the Schmidt coefficients is the squared norm of the state;
in particular, for a normalised state the squared Schmidt coefficients sum to `1`. -/
theorem schmidt_sum_sq {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) :
    ∑ k, (s k) ^ 2 = ∑ i, ∑ j, Complex.normSq (psi i j) := by
  obtain ⟨hs, hu, hv, hrec⟩ := h
  have hu' : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := hu
  have inner : ∀ i, ∑ j, psi i j * conj (psi i j)
      = ∑ k, ((s k : ℂ) * u k i) * ((s k : ℂ) * conj (u k i)) := by
    intro i
    have h1 : ∀ j, psi i j = ∑ k, ((s k : ℂ) * u k i) * v k j := fun j => hrec i j
    have h2 : ∀ j, conj (psi i j) = ∑ l, ((s l : ℂ) * conj (u l i)) * conj (v l j) := by
      intro j
      rw [hrec i j, map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        simp only [map_mul, Complex.conj_ofReal]
    calc ∑ j, psi i j * conj (psi i j)
        = ∑ j, (∑ k, ((s k : ℂ) * u k i) * v k j)
            * (∑ l, ((s l : ℂ) * conj (u l i)) * conj (v l j)) :=
          Finset.sum_congr rfl fun j _ => by rw [h2 j, h1 j]
      _ = ∑ k, ((s k : ℂ) * u k i) * ((s k : ℂ) * conj (u k i)) :=
          sum_mul_conj_of_orthonormal hv _ _
  have key : ∑ i, ∑ j, psi i j * conj (psi i j) = ∑ k, ((s k : ℂ)) ^ 2 := by
    simp only [inner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ i, ((s k : ℂ) * u k i) * ((s k : ℂ) * conj (u k i))
        = (s k : ℂ) ^ 2 * ∑ i, conj (u k i) * u k i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hu' k k]
    simp
  have hR : ((∑ i, ∑ j, Complex.normSq (psi i j) : ℝ) : ℂ) = ((∑ k, (s k) ^ 2 : ℝ) : ℂ) := by
    calc ((∑ i, ∑ j, Complex.normSq (psi i j) : ℝ) : ℂ)
        = ∑ i, ∑ j, psi i j * conj (psi i j) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Complex.normSq_eq_conj_mul_self]; ring
      _ = ∑ k, ((s k : ℂ)) ^ 2 := key
      _ = ((∑ k, (s k) ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  exact_mod_cast hR.symm

omit [DecidableEq B] in
/-- The Schmidt rank (the number of terms in a Schmidt decomposition) is unique. -/
theorem schmidt_rank_unique {r r' : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} {s' : Fin r' → ℝ} {u' : Fin r' → A → ℂ} {v' : Fin r' → B → ℂ}
    (h : IsSchmidtDecomposition psi s u v) (h' : IsSchmidtDecomposition psi s' u' v') :
    r = r' := by
  have hc := congrArg Multiset.card (schmidt_unique h h')
  simpa using hc

/-- **Schmidt decomposition.** Every bipartite pure state (given by its amplitudes
`psi i j` in a product basis) admits a Schmidt decomposition
`psi i j = ∑ k, s k * u k i * v k j` with positive Schmidt coefficients `s k` and
orthonormal families `u`, `v`; moreover the Schmidt coefficients are unique: any two
Schmidt decompositions of the same state have the same multiset of coefficients (in
particular the same number of terms, the Schmidt rank). -/
theorem schmidt_decomposition (psi : A → B → ℂ) :
    (∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → A → ℂ) (v : Fin r → B → ℂ),
        IsSchmidtDecomposition psi s u v) ∧
      (∀ (r r' : ℕ) (s : Fin r → ℝ) (u : Fin r → A → ℂ) (v : Fin r → B → ℂ)
        (s' : Fin r' → ℝ) (u' : Fin r' → A → ℂ) (v' : Fin r' → B → ℂ),
        IsSchmidtDecomposition psi s u v → IsSchmidtDecomposition psi s' u' v' →
        Multiset.map s Finset.univ.val = Multiset.map s' Finset.univ.val) :=
  ⟨exists_schmidt psi, fun _ _ _ _ _ _ _ _ h h' => schmidt_unique h h'⟩

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

