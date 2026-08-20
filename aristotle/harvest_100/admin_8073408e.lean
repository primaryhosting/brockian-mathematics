/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The proof follows the classical route: writing `A = U Dα U*`, `B = V Dβ V*` via the spectral
theorem, one gets `tr (A B) = ∑ j k, α j * β k * |W j k|²` for the unitary `W = U* V`.
The matrix of squared moduli of a unitary matrix is doubly stochastic, so by Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) the right-hand side is a convex combination of the
quantities `∑ j, α j * β (σ j)`, each of which is bounded by `∑ i, a i * b i` by the rearrangement
inequality (`Monovary.sum_mul_comp_perm_le_sum_mul`).
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a matrix. -/
noncomputable def weightMatrix (W : Matrix n n 𝕜) : Matrix n n ℝ := fun j k => ‖W j k‖ ^ 2

/-- The squared-modulus matrix of a unitary matrix is doubly stochastic. -/
lemma weightMatrix_mem_doublyStochastic {W : Matrix n n 𝕜} (h1 : W * star W = 1)
    (h2 : star W * W = 1) : weightMatrix W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun j k => by simp only [weightMatrix]; positivity, fun j => ?_, fun k => ?_⟩
  · have e : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = (W * star W) j j := by
      rw [Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.star_apply, show (star (W j k)) = starRingEnd 𝕜 (W j k) from rfl,
        RCLike.mul_conj]
    rw [h1, Matrix.one_apply_eq] at e
    simp only [weightMatrix]
    exact_mod_cast e
  · have e : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = (star W * W) k k := by
      rw [Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.star_apply, show (star (W j k)) = starRingEnd 𝕜 (W j k) from rfl,
        RCLike.conj_mul]
    rw [h2, Matrix.one_apply_eq] at e
    simp only [weightMatrix]
    exact_mod_cast e

/-- Trace of `diagonal a * W * diagonal b * star W` as a weighted double sum. -/
lemma trace_diagonal_conj (a b : n → ℝ) (W : Matrix n n 𝕜) :
    trace (diagonal (RCLike.ofReal ∘ a) * W * diagonal (RCLike.ofReal ∘ b) * star W)
      = ∑ j, ∑ k, ((a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
  have hM : diagonal (RCLike.ofReal ∘ a) * W * diagonal (RCLike.ofReal ∘ b)
      = Matrix.of fun j k => (a j : 𝕜) * W j k * (b k : 𝕜) := by
    ext j k
    rw [mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp [mul_assoc]
  rw [hM]
  simp only [trace, diag_apply, Matrix.mul_apply, star_apply, of_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show (star (W j k)) = starRingEnd 𝕜 (W j k) from rfl]
  push_cast
  rw [mul_assoc, mul_comm ((b k : 𝕜)), ← mul_assoc, mul_assoc _ (W j k), RCLike.mul_conj]
  ring

/-- For Hermitian `A`, `B` the real part of `tr (A * B)` is a doubly stochastic average of
products of eigenvalues. -/
lemma exists_doublyStochastic_trace_eq {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∃ S ∈ doublyStochastic ℝ n,
      RCLike.re (trace (A * B))
        = ∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * S j k := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary with hUdef
  set V : Matrix n n 𝕜 := ↑hB.eigenvectorUnitary with hVdef
  have hU1 : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : star V * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : V * star V = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have hA' : A = U * Da * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, mul_assoc, hDa, hUdef]
  have hB' : B = V * Db * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, mul_assoc, hDb, hVdef]
  set W : Matrix n n 𝕜 := star U * V with hW
  have hstarW : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hW1 : W * star W = 1 := by
    rw [hW, hstarW, mul_assoc, ← mul_assoc V, hV2, one_mul, hU1]
  have hW2 : star W * W = 1 := by
    rw [hW, hstarW, mul_assoc, ← mul_assoc U, hU2, one_mul, hV1]
  refine ⟨weightMatrix W, weightMatrix_mem_doublyStochastic hW1 hW2, ?_⟩
  have htr : trace (A * B) = trace (Da * W * Db * star W) := by
    have hprod : A * B = U * (Da * W * Db * star W) * star U := by
      rw [hA', hB', hW, hstarW]
      simp only [mul_assoc, hU2, mul_one]
    rw [hprod, trace_mul_comm, ← mul_assoc, hU1, one_mul]
  rw [htr, hDa, hDb, trace_diagonal_conj, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [weightMatrix]

omit [DecidableEq n] in
/-- Rearrangement step: for decreasing rearrangements `a`, `b` of `f`, `g`, and any permutation
`σ`, `∑ j, f j * g (σ j) ≤ ∑ i, a i * b i`. -/
lemma sum_perm_le_sum_sorted [LinearOrder n] {f g a b : n → ℝ} (ha : Antitone a)
    (hb : Antitone b) {sa sb : Equiv.Perm n} (hsa : a = f ∘ sa) (hsb : b = g ∘ sb)
    (σ : Equiv.Perm n) : ∑ j, f j * g (σ j) ≤ ∑ i, a i * b i := by
  have hmono : Monovary a b := by
    intro i j h
    rcases le_total i j with hij | hij
    · exact absurd (hb hij) (not_le.2 h)
    · exact ha hij
  have hf : ∀ i, f (sa i) = a i := fun i => by rw [hsa]; rfl
  have hg : ∀ k, g k = b (sb.symm k) := fun k => by rw [hsb]; simp
  have h1 : ∑ j, f j * g (σ j) = ∑ i, a i * b ((sa.trans (σ.trans sb.symm)) i) := by
    rw [← Equiv.sum_comp sa fun j => f j * g (σ j)]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hg]; rfl
  rw [h1]
  exact hmono.sum_mul_comp_perm_le_sum_mul

/-- Averaging step: a doubly stochastic average of the quantities `∑ j, f j * g (σ j)` is bounded
by any common upper bound `T` of those quantities. -/
lemma sum_doublyStochastic_le {f g : n → ℝ} {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n)
    (T : ℝ) (hT : ∀ σ : Equiv.Perm n, ∑ j, f j * g (σ j) ≤ T) :
    ∑ j, ∑ k, f j * g k * S j k ≤ T := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ j k, S j k = ∑ σ : Equiv.Perm n, w σ * (if σ j = k then 1 else 0) := by
    intro j k
    rw [← hwS]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have key : ∑ j, ∑ k, f j * g k * S j k = ∑ σ : Equiv.Perm n, w σ * ∑ j, f j * g (σ j) := by
    calc ∑ j, ∑ k, f j * g k * S j k
        = ∑ j, ∑ k, ∑ σ : Equiv.Perm n, w σ * (f j * g k * (if σ j = k then 1 else 0)) := by
          refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
          rw [hentry j k, Finset.mul_sum]
          exact sum_congr rfl fun σ _ => by ring
      _ = ∑ j, ∑ σ : Equiv.Perm n, ∑ k, w σ * (f j * g k * (if σ j = k then 1 else 0)) :=
          sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, ∑ j, ∑ k, w σ * (f j * g k * (if σ j = k then 1 else 0)) :=
          Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, w σ * ∑ j, f j * g (σ j) := by
          refine sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          exact sum_congr rfl fun j _ => by simp
  rw [key]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ j, f j * g (σ j)
      ≤ ∑ σ : Equiv.Perm n, w σ * T :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hT σ) (hw0 σ)
    _ = T := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Von Neumann trace inequality**, Hermitian case.

If `A` and `B` are Hermitian matrices over an `RCLike` field, and `a`, `b` are the eigenvalues of
`A` and `B` respectively, each sorted in decreasing order (i.e. `a`, `b` are antitone
rearrangements of the eigenvalue tuples), then `Re (tr (A * B)) ≤ ∑ i, a i * b i`. -/
theorem vonNeumann_trace_ineq_hermitian [LinearOrder n] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a b : n → ℝ} (ha : Antitone a) (hb : Antitone b)
    {sa sb : Equiv.Perm n} (hsa : a = hA.eigenvalues ∘ sa) (hsb : b = hB.eigenvalues ∘ sb) :
    RCLike.re (trace (A * B)) ≤ ∑ i, a i * b i := by
  obtain ⟨S, hS, hEq⟩ := exists_doublyStochastic_trace_eq hA hB
  rw [hEq]
  exact sum_doublyStochastic_le hS _ fun σ => sum_perm_le_sum_sorted ha hb hsa hsb σ

/-- Every real tuple admits a decreasing rearrangement. -/
lemma exists_antitone_perm {m : ℕ} (f : Fin m → ℝ) :
    ∃ σ : Equiv.Perm (Fin m), Antitone (f ∘ σ) := by
  refine ⟨Tuple.sort (fun i => -(f i)), fun i j hij => ?_⟩
  simpa using Tuple.monotone_sort (fun i => -(f i)) hij

/-- Von Neumann trace inequality, existence form: the decreasingly sorted eigenvalue tuples
exist, and satisfy `Re (tr (A * B)) ≤ ∑ i, a i * b i`. -/
theorem exists_sorted_eigenvalues_trace_le {m : ℕ} {A B : Matrix (Fin m) (Fin m) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ a b : Fin m → ℝ, Antitone a ∧ Antitone b ∧
      (∃ sa : Equiv.Perm (Fin m), a = hA.eigenvalues ∘ sa) ∧
      (∃ sb : Equiv.Perm (Fin m), b = hB.eigenvalues ∘ sb) ∧
      RCLike.re (trace (A * B)) ≤ ∑ i, a i * b i := by
  obtain ⟨sa, ha⟩ := exists_antitone_perm hA.eigenvalues
  obtain ⟨sb, hb⟩ := exists_antitone_perm hB.eigenvalues
  exact ⟨_, _, ha, hb, ⟨sa, rfl⟩, ⟨sb, rfl⟩,
    vonNeumann_trace_ineq_hermitian hA hB ha hb rfl rfl⟩

end Zeta23Core

