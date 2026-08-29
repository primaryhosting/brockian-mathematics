/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the header above is
-- written as a plain block comment; it is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `Dₐ W D_b Wᴴ`, for diagonal matrices with real entries `a`, `b`, expands as
`∑ j k, a j * b k * ‖W j k‖ ^ 2`. -/
theorem trace_diagonal_mul_mul_diagonal_mul_conjTranspose
    (W : Matrix n n 𝕜) (a b : n → ℝ) :
    Matrix.trace (diagonal (fun j => (a j : 𝕜)) * W * diagonal (fun k => (b k : 𝕜)) * Wᴴ)
      = ∑ j, ∑ k, ((a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ite_mul, zero_mul, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h : W j k * star (W j k) = ((‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
    simpa [RCLike.star_def] using RCLike.mul_conj (W j k)
  push_cast at h ⊢
  linear_combination ((a j : 𝕜) * (b k)) * h

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/
theorem normSq_entries_mem_doublyStochastic
    (W : Matrix n n 𝕜) (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  have h1 : W * Wᴴ = 1 := by simpa using (Unitary.mem_iff.mp hW).2
  have h2 : Wᴴ * W = 1 := by simpa using (Unitary.mem_iff.mp hW).1
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by dsimp; positivity, fun i => ?_, fun j => ?_⟩
  · have hd : ∑ k, W i k * (Wᴴ) k i = 1 := by
      have := congrFun (congrFun h1 i) i
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have h : ((∑ k, ‖W i k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      rw [RCLike.ofReal_sum, ← hd]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply]
      push_cast
      simpa [RCLike.star_def] using (RCLike.mul_conj (W i k)).symm
    exact_mod_cast h
  · have hd : ∑ k, (Wᴴ) j k * W k j = 1 := by
      have := congrFun (congrFun h2 j) j
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have h : ((∑ k, ‖W k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      rw [RCLike.ofReal_sum, ← hd]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply]
      push_cast
      simpa [RCLike.star_def] using (RCLike.conj_mul (W k j)).symm
    exact_mod_cast h

/-- Averaging a bilinear form against a doubly stochastic matrix cannot beat the value obtained by
pairing the two families in decreasing order.  Here `f` and `g` are antitone families indexed by
`Fin N`, transported to the index type `n` along an equivalence `e`. -/
theorem sum_mul_doublyStochastic_le_sum_mul {N : ℕ} (e : Fin N ≃ n)
    (f g : Fin N → ℝ) (hf : Antitone f) (hg : Antitone g)
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ j, ∑ k, f (e.symm j) * g (e.symm k) * S j k ≤ ∑ i, f i * g i := by
  have hmono : Monovary f g := by
    intro i j hij
    exact hf (le_of_not_ge fun h => absurd (hg h) (not_le.2 hij))
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∀ σ : Equiv.Perm n,
      ∑ j, ∑ k, f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k ≤ ∑ i, f i * g i := by
    intro σ
    have h1 : ∀ j : n, ∑ k, f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k
        = f (e.symm j) * g (e.symm (σ j)) := by
      intro j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [Finset.sum_congr rfl fun j _ => h1 j,
      ← Equiv.sum_comp e (fun j => f (e.symm j) * g (e.symm (σ j)))]
    simp only [Equiv.symm_apply_apply]
    exact hmono.sum_mul_comp_perm_le_sum_mul (σ := (e.trans σ).trans e.symm)
  have hSeq : ∀ j k, S j k = ∑ σ : Equiv.Perm n, w σ * (σ.permMatrix ℝ) j k := by
    intro j k
    rw [← hwS]
    simp [Matrix.sum_apply]
  have hswap : ∀ j : n, ∑ k, ∑ σ : Equiv.Perm n,
      f (e.symm j) * g (e.symm k) * (w σ * (σ.permMatrix ℝ) j k)
      = ∑ σ : Equiv.Perm n, ∑ k, w σ * (f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k) := by
    intro j
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun k _ => by ring
  calc ∑ j, ∑ k, f (e.symm j) * g (e.symm k) * S j k
      = ∑ σ : Equiv.Perm n, w σ *
          (∑ j, ∑ k, f (e.symm j) * g (e.symm k) * (σ.permMatrix ℝ) j k) := by
        simp only [hSeq, Finset.mul_sum]
        rw [Finset.sum_congr rfl fun j _ => hswap j, Finset.sum_comm]
    _ ≤ ∑ σ : Equiv.Perm n, w σ * (∑ i, f i * g i) :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, f i * g i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field, indexed by a finite type,
`Re (tr (A * B)) ≤ ∑ i, aᵢ * bᵢ`, where `a` and `b` are the eigenvalues of `A` and `B`,
each listed in decreasing order (`Matrix.IsHermitian.eigenvalues₀`). -/
theorem vonNeumann_trace_ineq_hermitian {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B)) ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  set a : n → ℝ := hA.eigenvalues with hadef
  set b : n → ℝ := hB.eigenvalues with hbdef
  set Da : Matrix n n 𝕜 := diagonal (fun j => (a j : 𝕜)) with hDa
  set Db : Matrix n n 𝕜 := diagonal (fun j => (b j : 𝕜)) with hDb
  have hAeq : A = U * Da * star U := hA.spectral_theorem
  have hBeq : B = V * Db * star V := hB.spectral_theorem
  have hUmem : U ∈ Matrix.unitaryGroup n 𝕜 := hA.eigenvectorUnitary.2
  have hVmem : V ∈ Matrix.unitaryGroup n 𝕜 := hB.eigenvectorUnitary.2
  have hUU : star U * U = 1 := (Unitary.mem_iff.mp hUmem).1
  have hUU' : U * star U = 1 := (Unitary.mem_iff.mp hUmem).2
  set W : Matrix n n 𝕜 := star U * V with hWdef
  have hWmem : W ∈ Matrix.unitaryGroup n 𝕜 :=
    mul_mem (Unitary.star_mem hUmem) hVmem
  have hWstar : star W = star V * U := by
    rw [hWdef, Matrix.star_mul, star_star]
  -- Reduce the trace of `A * B` to the trace of `Da * W * Db * Wᴴ`.
  have hprod : A * B = U * (Da * W * Db * star W) * star U := by
    rw [hAeq, hBeq, hWdef, hWstar]
    simp only [mul_assoc]
    rw [hUU', mul_one]
  have htrace : Matrix.trace (A * B) = Matrix.trace (Da * W * Db * star W) := by
    rw [hprod, Matrix.trace_mul_comm, ← mul_assoc, hUU, one_mul]
  -- Expand that trace as a weighted sum with doubly stochastic weights.
  have hWH : star W = Wᴴ := rfl
  have hexp : Matrix.trace (A * B) = ∑ j, ∑ k, ((a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
    rw [htrace, hWH, hDa, hDb]
    exact trace_diagonal_mul_mul_diagonal_mul_conjTranspose W a b
  have hre : RCLike.re (Matrix.trace (A * B)) = ∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 := by
    rw [hexp]
    simp only [← RCLike.ofReal_sum, RCLike.ofReal_re]
  rw [hre]
  -- Apply the doubly stochastic rearrangement bound.
  set e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with hedef
  have ha : ∀ j, a j = hA.eigenvalues₀ (e.symm j) := fun j => rfl
  have hb : ∀ j, b j = hB.eigenvalues₀ (e.symm j) := fun j => rfl
  have hS : (Matrix.of fun j k => ‖W j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n :=
    normSq_entries_mem_doublyStochastic W hWmem
  have := sum_mul_doublyStochastic_le_sum_mul e hA.eigenvalues₀ hB.eigenvalues₀
    hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone hS
  simpa only [ha, hb, Matrix.of_apply] using this

end Zeta23Core

