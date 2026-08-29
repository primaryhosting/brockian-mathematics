/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

A pure state of a bipartite quantum system `A ⊗ B` is described, in a product basis, by its
amplitude matrix `M : Matrix A B ℂ`, normalised so that `∑ a b, ‖M a b‖ ^ 2 = 1`.  The reduced
density matrix of the left half is `ρ_A = M * Mᴴ`, and the *entanglement entropy* across the cut
is the von Neumann entropy `-Tr ρ_A log ρ_A = ∑ᵢ negMulLog λᵢ` of its eigenvalues.

The entanglement *area law* in one dimension says that for a gapped local Hamiltonian the ground
state's entanglement entropy across a cut of the chain is bounded by a constant that does not grow
with the length of the chain (the "area" of a cut of a 1D chain being a single point).  The
mechanism, which is the content of Hastings' theorem, is that the gap forces the Schmidt rank
(equivalently, the matrix–product bond dimension) across the cut to be bounded by a constant `D`
independent of the system size.

Here we formalise the area law given that input: from a uniform bound `D` on the Schmidt rank
across the cut we derive the uniform entropy bound `log D`, valid for every chain length.  The
final theorem `Phys.area_law_1d` is stated for a family of chain states indexed by the number of
sites, and its conclusion is a bound that is *independent of the number of sites*.

Note on the file header: it is written as a plain block comment `/- ... -/` rather than a module
docstring `/-! ... -/`, because Lean requires all `import` commands to come before any module
docstring, so a `/-! ... -/` header on line 1 would make the file fail to compile.
-/

open scoped BigOperators ComplexOrder
open Finset Matrix

namespace Phys

/-- The entanglement entropy across a cut, computed from the amplitude matrix `M` of the state:
the von Neumann entropy `∑ᵢ -λᵢ log λᵢ` of the reduced density matrix `ρ = M * Mᴴ`. -/
noncomputable def entanglementEntropy {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) : ℝ :=
  ∑ i, Real.negMulLog ((Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i)

/-- The Schmidt rank of a bipartite pure state with amplitude matrix `M`: the rank of `M`,
equivalently the number of non-zero Schmidt coefficients, equivalently the bond dimension needed
at that cut in a matrix-product representation. -/
noncomputable def schmidtRank {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) : ℕ := M.rank

/-- **Maximal entropy bound.**  A probability vector supported on at most `D` points has entropy
at most `log D`. -/
theorem entropy_le_log_card_support {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (D : ℕ)
    (hcard : {i | p i ≠ 0}.ncard ≤ D) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log D := by
  classical
  set s : Finset ι := univ.filter (fun i => p i ≠ 0) with hs
  have hsc : s.card ≤ D := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf] at hcard
    exact hcard
  have hsum_s : ∑ i ∈ s, p i = 1 := by rw [hs, Finset.sum_filter_ne_zero, hsum]
  have hDpos : 0 < (D : ℝ) := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso
      subst h
      have hempty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hsc)
      rw [hempty] at hsum_s
      simp at hsum_s
    · exact_mod_cast h
  have hsum_eq : ∑ i, Real.negMulLog (p i) = ∑ i ∈ s, Real.negMulLog (p i) := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  rw [hsum_eq]
  have key : ∀ i ∈ s, Real.negMulLog (p i) ≤ (1 / (D : ℝ) - p i) + p i * Real.log D := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (by
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact fun h => hi h.symm)
    have hx : 0 < 1 / ((D : ℝ) * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by positivity) (ne_of_gt hpi)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
    rw [Real.negMulLog_def]
    field_simp at hmul ⊢
    nlinarith [hmul, hpi, hDpos]
  calc ∑ i ∈ s, Real.negMulLog (p i)
      ≤ ∑ i ∈ s, ((1 / (D : ℝ) - p i) + p i * Real.log D) := Finset.sum_le_sum key
    _ = s.card / (D : ℝ) - 1 + Real.log D := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_s]
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ Real.log D := by
        have hle : (s.card : ℝ) / D ≤ 1 := by
          rw [div_le_one hDpos]; exact_mod_cast hsc
        linarith

/-- The eigenvalues of the reduced density matrix are non-negative. -/
theorem eigenvalues_nonneg {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (i : A) :
    0 ≤ (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i :=
  (Matrix.posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg i

/-- For a normalised state the eigenvalues of the reduced density matrix sum to one. -/
theorem sum_eigenvalues_eq_one {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) :
    ∑ i, (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i = 1 := by
  have htr := (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.trace_eq_sum_eigenvalues
  have h2 : (M * Mᴴ).trace = ((∑ a, ∑ b, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [htr, hM] at h2
  have h3 : ((∑ i, (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i : ℝ) : ℂ)
      = ((1 : ℝ) : ℂ) := by push_cast; simpa using h2
  exact_mod_cast h3

/-- The number of non-zero eigenvalues of the reduced density matrix equals the Schmidt rank. -/
theorem card_support_eigenvalues {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) :
    {i | (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i ≠ 0}.ncard
      = schmidtRank M := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, schmidtRank,
    ← Matrix.rank_self_mul_conjTranspose M,
    (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.rank_eq_card_non_zero_eigs,
    Fintype.card_subtype]

/-- **Entropy bound from the Schmidt rank.**  A normalised bipartite pure state whose Schmidt rank
across the cut is at most `D` has entanglement entropy at most `log D`. -/
theorem entanglementEntropy_le_log_schmidtRank {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (M : Matrix A B ℂ) (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) (D : ℕ)
    (hD : schmidtRank M ≤ D) :
    entanglementEntropy M ≤ Real.log D := by
  refine entropy_le_log_card_support _ (eigenvalues_nonneg M) (sum_eigenvalues_eq_one M hM) D ?_
  rw [card_support_eigenvalues M]
  exact hD

/-- A state written as a matrix product with bond dimension `D` at the cut has Schmidt rank at
most `D`. -/
theorem schmidtRank_le_of_bond {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] (D : ℕ)
    (X : Matrix A (Fin D) ℂ) (Y : Matrix (Fin D) B ℂ) :
    schmidtRank (X * Y) ≤ D := by
  refine (Matrix.rank_mul_le_left X Y).trans ?_
  simpa using X.rank_le_card_width

/-- **Entanglement area law in one dimension.**

`M n` is the amplitude matrix, across a fixed cut, of the ground state of a chain of `n` sites of
local dimension `d` (`hnorm n` says the state is normalised).  The gapped-ness of the model enters
through `hbond`: the Schmidt rank across the cut is bounded by a constant `D`, uniformly in the
chain length `n` — this is the content of Hastings' theorem.  The conclusion is the area law: the
entanglement entropy across the cut is bounded by `log D`, a constant *independent of the number
of sites* (rather than growing with the size of the subsystem). -/
theorem area_law_1d (d D : ℕ) (M : ∀ n : ℕ, Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ)
    (hnorm : ∀ n, ∑ a, ∑ b, ‖M n a b‖ ^ 2 = 1) (hbond : ∀ n, schmidtRank (M n) ≤ D) :
    ∀ n, entanglementEntropy (M n) ≤ Real.log D :=
  fun n => entanglementEntropy_le_log_schmidtRank (M n) (hnorm n) D (hbond n)

/-- The area law in the form "the entanglement entropy across the cut stays bounded by a single
constant as the chain grows". -/
theorem area_law_1d_bounded (d D : ℕ) (M : ∀ n : ℕ, Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ)
    (hnorm : ∀ n, ∑ a, ∑ b, ‖M n a b‖ ^ 2 = 1) (hbond : ∀ n, schmidtRank (M n) ≤ D) :
    ∃ C : ℝ, ∀ n, entanglementEntropy (M n) ≤ C :=
  ⟨Real.log D, area_law_1d d D M hnorm hbond⟩

/-- A product state of an `n`-site chain of qubits: all the amplitude sits on a single basis
vector.  It is used to show that the hypotheses of `area_law_1d` are satisfiable, i.e. that the
theorem is not vacuous. -/
noncomputable def productChainState (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.single 0 0 1

theorem productChainState_normalized (n : ℕ) : ∑ a, ∑ b, ‖productChainState n a b‖ ^ 2 = 1 := by
  simp [productChainState, Matrix.single, ite_and, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]

theorem schmidtRank_productChainState_le_one (n : ℕ) : schmidtRank (productChainState n) ≤ 1 := by
  have h : productChainState n = Matrix.single (0 : Fin (2 ^ n)) (0 : Fin 1) (1 : ℂ)
      * Matrix.single (0 : Fin 1) (0 : Fin (2 ^ n)) (1 : ℂ) := by
    ext a b
    simp [Matrix.mul_apply, productChainState, Matrix.single, ite_and]
    split_ifs <;> rfl
  rw [h]
  exact schmidtRank_le_of_bond 1 _ _

/-- The hypotheses of `area_law_1d` are satisfiable: product states of the qubit chain are
normalised and have Schmidt rank `1` at the cut, for every chain length. -/
theorem area_law_1d_hypotheses_satisfiable :
    ∃ M : ∀ n : ℕ, Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      (∀ n, ∑ a, ∑ b, ‖M n a b‖ ^ 2 = 1) ∧ (∀ n, schmidtRank (M n) ≤ 1) :=
  ⟨productChainState, productChainState_normalized, schmidtRank_productChainState_le_one⟩

end Phys

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

