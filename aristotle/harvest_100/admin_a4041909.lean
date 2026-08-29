/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is reproduced verbatim as a module docstring below; Lean 4 requires
-- `import` commands to precede any module docstring.)

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

/-!
## Overview

Hastings' area law states that the ground state of a gapped local Hamiltonian on a
one-dimensional chain has entanglement entropy across any cut bounded by a constant,
independent of the length of the chain and of the position of the cut.  The mechanism
behind the theorem is that such a ground state is (approximated by) a *finitely
correlated state* / *matrix product state* of bounded bond dimension `D`; a state with
a bond dimension `D` across a cut has Schmidt rank at most `D`, hence entanglement
entropy at most `log D`.

Here we formalize this final, mathematical content of the area law: for a matrix
product state on a chain of `k + m` sites built from `D × D` transfer matrices, the
von Neumann entropy of the reduced density matrix of the first `k` sites is at most
`log D`, *uniformly in `k` and `m`*.  This is the quantitative area-law bound: a
constant, independent of the subsystem size and of the total system size (in one
dimension the boundary of an interval consists of a bounded number of points, so a
constant bound *is* an area law).  The physical input of Hastings' theorem — that a
gapped local Hamiltonian has a ground state of this form — is an approximation
statement about Hamiltonians and is not part of the formalization below.

The two mathematical ingredients that are proved from scratch are:

* `Phys.entropy_le_log_of_card_support_le` — the maximum-entropy bound: a probability
  vector supported on at most `D` outcomes has Shannon entropy at most `log D`;
* `Phys.cutMatrix_eq_mul` — the matrix product structure factors the coefficient
  matrix of the state across the cut through a `D`-dimensional space, so the reduced
  density matrix has rank at most `D`.
-/

namespace Phys

open Matrix Finset

/-! ## Shannon entropy and the maximum entropy bound -/

/-- Shannon (von Neumann) entropy of a finite family of numbers,
`H(p) = -∑ pᵢ log pᵢ`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- **Maximum entropy bound.**  A probability vector whose support has at most `D`
elements has entropy at most `log D`. -/
theorem entropy_le_log_of_card_support_le {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (D : ℕ)
    (hcard : #{i | p i ≠ 0} ≤ D) :
    entropy p ≤ Real.log D := by
  classical
  rw [entropy]
  set s : Finset ι := {i | p i ≠ 0} with hs
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · exfalso
      have hz : ∀ i ∈ (Finset.univ : Finset ι), p i = 0 := by
        intro i _
        by_contra hi
        exact absurd (by simp [hs, hi] : i ∈ s) (by simp [h])
      rw [Finset.sum_congr rfl hz] at hsum
      simp at hsum
    · exact h
  have hD : 1 ≤ D := le_trans (Finset.card_pos.mpr hsne) hcard
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum_s : ∑ i ∈ s, p i = 1 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.subset_univ s) ?_
    intro i _ hi
    simpa [hs] using hi
  have hent : -∑ i, p i * Real.log (p i) = -∑ i ∈ s, p i * Real.log (p i) := by
    congr 1
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    have : p i = 0 := by simpa [hs] using hi
    simp [this]
  rw [hent]
  have key : ∀ i ∈ s, -(p i * Real.log (p i)) - p i * Real.log D ≤ 1 / (D : ℝ) - p i := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (by simpa [hs] using hi))
    have h1 : Real.log (1 / (p i * D)) ≤ 1 / (p i * D) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (1 / (p i * D)) = -Real.log (p i) - Real.log D := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hpi) (ne_of_gt hDpos)]
      ring
    have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hpi)
    rw [h2] at h3
    calc -(p i * Real.log (p i)) - p i * Real.log D
        = p i * (-Real.log (p i) - Real.log D) := by ring
      _ ≤ p i * (1 / (p i * D) - 1) := h3
      _ = 1 / (D : ℝ) - p i := by field_simp
  have hsum2 : ∑ i ∈ s, (-(p i * Real.log (p i)) - p i * Real.log D)
      ≤ ∑ i ∈ s, (1 / (D : ℝ) - p i) := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_s] at hsum2
  simp only [Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul] at hsum2
  have hcards : (s.card : ℝ) ≤ D := by exact_mod_cast hcard
  have hfin : (s.card : ℝ) * (1 / (D : ℝ)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hDpos).mpr hcards
  linarith [hsum2]

/-! ## Matrix product states on a one-dimensional chain -/

variable {S : Type*} {D : ℕ}

/-- `prodMat A s len start` is the ordered product `A_start(s_start) ⋯ A_{start+len-1}(s_{start+len-1})`
of the MPS transfer matrices along `len` consecutive sites of the chain, in the
configuration `s`. -/
noncomputable def prodMat (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ) (s : ℕ → S) :
    ℕ → ℕ → Matrix (Fin D) (Fin D) ℂ
  | 0, _ => 1
  | (len + 1), start => A start (s start) * prodMat A s len (start + 1)

/-- The transfer-matrix product only depends on the configuration at the sites it covers. -/
lemma prodMat_congr (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ) (s t : ℕ → S) (len start : ℕ)
    (h : ∀ i, start ≤ i → i < start + len → s i = t i) :
    prodMat A s len start = prodMat A t len start := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      have h0 : s start = t start := h start le_rfl (by omega)
      rw [prodMat, prodMat, h0, ih (start + 1) fun i hi hi2 => h i (by omega) (by omega)]

/-- Splitting the chain into two consecutive blocks splits the transfer-matrix product. -/
lemma prodMat_add (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ) (s : ℕ → S) (k m start : ℕ) :
    prodMat A s (k + m) start = prodMat A s k start * prodMat A s m (start + k) := by
  induction k generalizing start with
  | zero => simp [prodMat]
  | succ k ih =>
      have e1 : k + 1 + m = (k + m) + 1 := by omega
      have e2 : start + 1 + k = start + (k + 1) := by omega
      rw [e1, prodMat, ih (start + 1), prodMat, mul_assoc, e2]

/-- The amplitude that the matrix product state with tensors `A` and boundary vectors
`vL`, `vR` assigns to the configuration `s` of a chain of `n` sites. -/
noncomputable def mpsAmp (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (n : ℕ) (s : ℕ → S) : ℂ :=
  vL ⬝ᵥ (prodMat A s n 0 *ᵥ vR)

/-- Merge a configuration `x` of the first `k` sites with a configuration `y` of the
next `m` sites into a configuration of the whole chain. -/
def mergeCfg [Inhabited S] (k : ℕ) {m : ℕ} (x : Fin k → S) (y : Fin m → S) : ℕ → S :=
  fun i => if h : i < k then x ⟨i, h⟩ else if h2 : i - k < m then y ⟨i - k, h2⟩ else default

/-- The coefficient matrix of the state across the cut separating the first `k` sites
from the remaining `m` sites: rows are configurations of the left block, columns are
configurations of the right block. -/
noncomputable def cutMatrix [Inhabited S] (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ)
    (vL vR : Fin D → ℂ) (k m : ℕ) : Matrix (Fin k → S) (Fin m → S) ℂ :=
  Matrix.of fun x y => mpsAmp A vL vR (k + m) (mergeCfg k x y)

/-- The left factor of the coefficient matrix: the boundary vector transported through
the left block; it takes values in the `D`-dimensional bond space. -/
noncomputable def leftBlock [Inhabited S] (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ)
    (vL : Fin D → ℂ) (k : ℕ) : Matrix (Fin k → S) (Fin D) ℂ :=
  Matrix.of fun x c => (vL ᵥ* prodMat A (mergeCfg k x (fun _ : Fin 0 => default)) k 0) c

/-- The right factor of the coefficient matrix: the boundary vector transported through
the right block, starting from the `D`-dimensional bond space. -/
noncomputable def rightBlock [Inhabited S] (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ)
    (vR : Fin D → ℂ) (k m : ℕ) : Matrix (Fin D) (Fin m → S) ℂ :=
  Matrix.of fun c y =>
    (prodMat A (mergeCfg k (fun _ : Fin k => default) y) m k *ᵥ vR) c

/-- **The bond-dimension factorization.**  Across any cut, the coefficient matrix of a
matrix product state factors through the `D`-dimensional bond space. -/
theorem cutMatrix_eq_mul [Inhabited S] (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ)
    (vL vR : Fin D → ℂ) (k m : ℕ) :
    cutMatrix A vL vR k m = leftBlock A vL k * rightBlock A vR k m := by
  ext x y
  have hL : prodMat A (mergeCfg k x y) k 0
      = prodMat A (mergeCfg k x (fun _ : Fin 0 => default)) k 0 := by
    refine prodMat_congr _ _ _ _ _ fun i _ hi => ?_
    have hik : i < k := by omega
    simp [mergeCfg, hik]
  have hR : prodMat A (mergeCfg k x y) m k
      = prodMat A (mergeCfg k (fun _ : Fin k => default) y) m k := by
    refine prodMat_congr _ _ _ _ _ fun i hi hi2 => ?_
    have hik : ¬ i < k := by omega
    have him : i - k < m := by omega
    simp [mergeCfg, hik, him]
  simp only [cutMatrix, leftBlock, rightBlock, Matrix.of_apply, mpsAmp]
  rw [prodMat_add, zero_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hL, hR,
    Matrix.mul_apply]
  rfl

/-! ## The reduced density matrix and its entropy -/

/-- The reduced density matrix `ρ = M Mᴴ` of the left block, for a state with
coefficient matrix `M`. -/
noncomputable def reducedDensity {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℂ) : Matrix α α ℂ := M * Mᴴ

lemma reducedDensity_isHermitian {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) :
    (reducedDensity M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M

/-- The entanglement entropy of a bipartite state given by its coefficient matrix `M`:
the von Neumann entropy of the reduced density matrix `M Mᴴ`. -/
noncomputable def entEntropy {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix α β ℂ) : ℝ :=
  entropy (reducedDensity_isHermitian M).eigenvalues

lemma trace_reducedDensity {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) :
    (reducedDensity M).trace = ((∑ x, ∑ y, ‖M x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [reducedDensity, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

lemma sum_eigenvalues_reducedDensity {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix α β ℂ) (h : ∑ x, ∑ y, ‖M x y‖ ^ 2 = 1) :
    ∑ i, (reducedDensity_isHermitian M).eigenvalues i = 1 := by
  have h1 := (reducedDensity_isHermitian M).trace_eq_sum_eigenvalues
  rw [trace_reducedDensity, h] at h1
  have : ((∑ i, (reducedDensity_isHermitian M).eigenvalues i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast at h1 ⊢
    exact h1.symm
  exact_mod_cast this

lemma eigenvalues_reducedDensity_nonneg {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix α β ℂ) (i : α) : 0 ≤ (reducedDensity_isHermitian M).eigenvalues i :=
  Matrix.eigenvalues_self_mul_conjTranspose_nonneg M i

/-- The rank of the reduced density matrix bounds the size of the support of its
spectrum. -/
lemma card_support_eigenvalues_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix α β ℂ) :
    #{i | (reducedDensity_isHermitian M).eigenvalues i ≠ 0} = (reducedDensity M).rank := by
  rw [(reducedDensity_isHermitian M).rank_eq_card_non_zero_eigs, Fintype.card_subtype]

/-! ## The area law -/

/-- **Area law for one-dimensional gapped ground states (matrix product form).**

Let a state of a one-dimensional chain of `k + m` sites (each site carrying the finite
local alphabet `S`) be a matrix product state with bond dimension `D`, i.e. built from
transfer matrices `A i : S → Matrix (Fin D) (Fin D) ℂ` and boundary vectors `vL`, `vR`.
If the state is normalized, then the entanglement entropy across the cut between the
first `k` sites and the last `m` sites is at most `log D`.

The bound is uniform in `k` and `m`: it depends neither on the size of the subsystem
nor on the size of the chain, only on the bond dimension.  This is the area law — in
one dimension the boundary of an interval is a bounded set of points, so the
entanglement entropy is bounded by a constant.  (Hastings' theorem provides the
physical input that a gapped local Hamiltonian has a ground state of this form with
bond dimension controlled by the spectral gap; that approximation statement is not
part of this formalization.) -/
theorem area_law_1d {S : Type*} [Fintype S] [DecidableEq S] [Inhabited S] {D : ℕ}
    (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ) (k m : ℕ)
    (hnorm : ∑ x : Fin k → S, ∑ y : Fin m → S, ‖cutMatrix A vL vR k m x y‖ ^ 2 = 1) :
    entEntropy (cutMatrix A vL vR k m) ≤ Real.log D := by
  classical
  set M := cutMatrix A vL vR k m with hM
  have hrank : (reducedDensity M).rank ≤ D := by
    have h1 : (reducedDensity M).rank = M.rank := by
      rw [reducedDensity, Matrix.rank_self_mul_conjTranspose]
    rw [h1, hM, cutMatrix_eq_mul]
    calc (leftBlock A vL k * rightBlock A vR k m).rank
        ≤ (leftBlock A vL k).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin D) := Matrix.rank_le_card_width _
      _ = D := Fintype.card_fin D
  refine entropy_le_log_of_card_support_le _ (eigenvalues_reducedDensity_nonneg M)
    (sum_eigenvalues_reducedDensity M hnorm) D ?_
  rw [card_support_eigenvalues_le]
  exact hrank

/-- **Uniform form of the area law.**  For a matrix product state of bond dimension `D`
the entanglement entropy across every cut of every chain is bounded by the single
constant `log D`, independently of the position of the cut and of the length of the
chain. -/
theorem area_law_1d_uniform {S : Type*} [Fintype S] [DecidableEq S] [Inhabited S] {D : ℕ}
    (A : ℕ → S → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ) :
    ∃ C : ℝ, ∀ k m : ℕ,
      (∑ x : Fin k → S, ∑ y : Fin m → S, ‖cutMatrix A vL vR k m x y‖ ^ 2 = 1) →
      entEntropy (cutMatrix A vL vR k m) ≤ C :=
  ⟨Real.log D, fun k m hnorm => area_law_1d A vL vR k m hnorm⟩

/-! ## Non-vacuity

The normalization hypothesis of `area_law_1d` is satisfiable: below is the trivial
(bond dimension one) product state of a chain whose local alphabet has one element. -/

lemma prodMat_one {S : Type*} (s : ℕ → S) (n start : ℕ) :
    prodMat (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) s n start = 1 := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => rw [prodMat, ih, one_mul]

example (k m : ℕ) :
    ∑ x : Fin k → Fin 1, ∑ y : Fin m → Fin 1,
      ‖cutMatrix (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ => 1) (fun _ => 1)
        k m x y‖ ^ 2 = 1 := by
  have hentry : ∀ (x : Fin k → Fin 1) (y : Fin m → Fin 1),
      cutMatrix (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun _ => 1) (fun _ => 1) k m x y
        = 1 := by
    intro x y
    simp [cutMatrix, mpsAmp, prodMat_one, dotProduct]
  simp [hentry]

end Phys

