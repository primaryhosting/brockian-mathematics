/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/
lemma sqAbs_mem_doublyStochastic {W : Matrix n n 𝕜} (h1 : W * star W = 1)
    (h2 : star W * W = 1) :
    (Matrix.of fun p q => ‖W p q‖ ^ 2) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj, Matrix.one_apply_eq] at h
    have hc : ((∑ q, ‖W i q‖ ^ 2 : ℝ) : 𝕜) = (1 : 𝕜) := by push_cast; simpa using h
    simpa using (by exact_mod_cast hc : (∑ q, ‖W i q‖ ^ 2 : ℝ) = 1)
  · have h := congrFun (congrFun h2 j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, RCLike.conj_mul, Matrix.one_apply_eq] at h
    have hc : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : 𝕜) = (1 : 𝕜) := by push_cast; simpa using h
    simpa using (by exact_mod_cast hc : (∑ i, ‖W i j‖ ^ 2 : ℝ) = 1)

/-- Expansion of the trace of `diagonal da * W * diagonal db * Wᴴ`. -/
lemma trace_diagonal_conj (da db : n → ℝ) (W : Matrix n n 𝕜) :
    Matrix.trace (diagonal (RCLike.ofReal ∘ da) * W * diagonal (RCLike.ofReal ∘ db) * star W)
      = ∑ p, ∑ q, ((da p * db q * ‖W p q‖ ^ 2 : ℝ) : 𝕜) := by
  have key : diagonal (RCLike.ofReal ∘ da) * W * diagonal (RCLike.ofReal ∘ db)
      = Matrix.of (fun p q => ((da p : 𝕜)) * W p q * (db q : 𝕜)) := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp
  rw [key, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.of_apply, Matrix.star_apply, RCLike.star_def]
  push_cast
  rw [mul_assoc, mul_comm ((db q : 𝕜)) _, ← mul_assoc, mul_assoc ((da p : 𝕜)) (W p q),
    RCLike.mul_conj]
  ring

/-- The trace of `A * B` for Hermitian `A`, `B`, written in terms of the eigenvalues and the
unitary `W` connecting the two eigenbases. -/
lemma trace_mul_eq_trace_diagonal_conj {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    Matrix.trace (A * B)
      = Matrix.trace (diagonal (RCLike.ofReal ∘ hA.eigenvalues)
          * (star (hA.eigenvectorUnitary : Matrix n n 𝕜) * (hB.eigenvectorUnitary : Matrix n n 𝕜))
          * diagonal (RCLike.ofReal ∘ hB.eigenvalues)
          * star (star (hA.eigenvectorUnitary : Matrix n n 𝕜)
              * (hB.eigenvectorUnitary : Matrix n n 𝕜))) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  have hUU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.2
  have hAeq := hA.spectral_theorem
  have hBeq := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hAeq hBeq
  rw [← hU] at hAeq
  rw [← hV] at hBeq
  rw [Matrix.star_mul, star_star]
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have key : U * (Da * (star U * V) * Db * (star V * U)) * star U = A * B := by
    rw [hAeq, hBeq]
    simp only [mul_assoc, hUU, mul_one]
  rw [← key, Matrix.trace_mul_comm, ← mul_assoc, hUU', one_mul]

/-- `Re tr(AB) = ∑_{p,q} α_p β_q |W_{pq}|²` where `W` is the unitary connecting the two
eigenbases. -/
lemma re_trace_mul_eq {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B))
      = ∑ p, ∑ q, hA.eigenvalues p * hB.eigenvalues q *
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
            (hB.eigenvectorUnitary : Matrix n n 𝕜)) p q‖ ^ 2 := by
  rw [trace_mul_eq_trace_diagonal_conj hA hB, trace_diagonal_conj, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => RCLike.ofReal_re _

/-- Two antitone functions monovary. -/
lemma monovary_of_antitone {N : ℕ} {a b : Fin N → ℝ} (ha : Antitone a) (hb : Antitone b) :
    Monovary a b := by
  intro i j h
  rcases le_total i j with hij | hij
  · exact absurd (hb hij) (not_le.2 h)
  · exact ha hij

/-- Rearrangement bound for a doubly stochastic weight matrix: a doubly stochastic average of
the products of two families of reals is at most the sum of the products of their decreasing
rearrangements. -/
lemma sum_doublyStochastic_le {N : ℕ} {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n)
    (al be : n → ℝ) (a b : Fin N → ℝ) (ea eb : Fin N ≃ n)
    (ha : ∀ i, a i = al (ea i)) (hb : ∀ i, b i = be (eb i))
    (ha' : Antitone a) (hb' : Antitone b) :
    ∑ p, ∑ q, al p * be q * S p q ≤ ∑ i, a i * b i := by
  classical
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSentry : ∀ p q, S p q = ∑ σ : Equiv.Perm n, w σ * (if σ p = q then 1 else 0) := by
    intro p q
    rw [← hwS]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hperm : ∀ σ : Equiv.Perm n, ∑ p, al p * be (σ p) ≤ ∑ i, a i * b i := by
    intro σ
    have h1 : ∑ p, al p * be (σ p)
        = ∑ i, a i * b ((ea.trans (σ.trans eb.symm) : Equiv.Perm (Fin N)) i) := by
      refine (Fintype.sum_equiv ea _ _ ?_).symm
      intro i
      simp [ha, hb]
    rw [h1]
    simpa [smul_eq_mul] using
      (monovary_of_antitone ha' hb').sum_smul_comp_perm_le_sum_smul
        (σ := (ea.trans (σ.trans eb.symm) : Equiv.Perm (Fin N)))
  have hmain : ∑ p, ∑ q, al p * be q * S p q = ∑ σ : Equiv.Perm n, w σ * ∑ p, al p * be (σ p) := by
    calc ∑ p, ∑ q, al p * be q * S p q
        = ∑ p, ∑ σ : Equiv.Perm n, w σ * (al p * be (σ p)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [hSentry, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          ring
      _ = ∑ σ : Equiv.Perm n, w σ * ∑ p, al p * be (σ p) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
  rw [hmain]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ p, al p * be (σ p)
      ≤ ∑ σ : Equiv.Perm n, w σ * ∑ i, a i * b i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hperm σ) (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/--
**Von Neumann trace inequality, Hermitian case.**

If `A` and `B` are Hermitian matrices over an `RCLike` field indexed by a finite type `n`, and
`a`, `b : Fin N → ℝ` list the eigenvalues of `A` and `B` respectively (i.e. each is the family of
eigenvalues reindexed by an equivalence `Fin N ≃ n`) in decreasing order, then
`Re tr(A * B) ≤ ∑ i, a i * b i`.
-/
theorem vonNeumann_trace_ineq_hermitian {N : ℕ} {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (a b : Fin N → ℝ) (ea eb : Fin N ≃ n)
    (ha : ∀ i, a i = hA.eigenvalues (ea i)) (hb : ∀ i, b i = hB.eigenvalues (eb i))
    (ha' : Antitone a) (hb' : Antitone b) :
    RCLike.re (Matrix.trace (A * B)) ≤ ∑ i, a i * b i := by
  classical
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set W : Matrix n n 𝕜 := star U * V with hW
  have hWs : W * star W = 1 := by
    rw [hW, StarMul.star_mul, star_star, mul_assoc, ← mul_assoc V (star V) U,
      (Matrix.mem_unitaryGroup_iff).1 hB.eigenvectorUnitary.2, one_mul,
      (Matrix.mem_unitaryGroup_iff').1 hA.eigenvectorUnitary.2]
  have hWs' : star W * W = 1 := by
    rw [hW, StarMul.star_mul, star_star, mul_assoc, ← mul_assoc U (star U) V,
      (Matrix.mem_unitaryGroup_iff).1 hA.eigenvectorUnitary.2, one_mul,
      (Matrix.mem_unitaryGroup_iff').1 hB.eigenvectorUnitary.2]
  have hS := sqAbs_mem_doublyStochastic hWs hWs'
  rw [re_trace_mul_eq hA hB]
  exact sum_doublyStochastic_le hS hA.eigenvalues hB.eigenvalues a b ea eb ha hb ha' hb'

omit [DecidableEq n] in
/-- Any family of reals indexed by a finite type can be reindexed by `Fin (card n)` so as to be
decreasing. -/
lemma exists_antitone_reindex (f : n → ℝ) :
    ∃ e : Fin (Fintype.card n) ≃ n, Antitone (f ∘ e) := by
  classical
  set eqv : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm with heqv
  set g : Fin (Fintype.card n) → ℝ := fun i => -(f (eqv i)) with hg
  refine ⟨(Tuple.sort g).trans eqv, ?_⟩
  have hm : Monotone (g ∘ Tuple.sort g) := Tuple.monotone_sort g
  intro i j hij
  have h := hm hij
  simp only [Function.comp_apply, hg] at h ⊢
  simpa using neg_le_neg h

/-- **Von Neumann trace inequality, Hermitian case**, in the form asserting existence of the
decreasing rearrangements of the two eigenvalue families. -/
theorem vonNeumann_trace_ineq_hermitian_sorted {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ ea eb : Fin (Fintype.card n) ≃ n,
      Antitone (hA.eigenvalues ∘ ea) ∧ Antitone (hB.eigenvalues ∘ eb) ∧
        RCLike.re (Matrix.trace (A * B))
          ≤ ∑ i, hA.eigenvalues (ea i) * hB.eigenvalues (eb i) := by
  obtain ⟨ea, hea⟩ := exists_antitone_reindex hA.eigenvalues
  obtain ⟨eb, heb⟩ := exists_antitone_reindex hB.eigenvalues
  exact ⟨ea, eb, hea, heb,
    vonNeumann_trace_ineq_hermitian hA hB _ _ ea eb (fun _ => rfl) (fun _ => rfl) hea heb⟩

end Zeta23Core

