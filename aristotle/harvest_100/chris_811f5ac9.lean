import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Monogamy of entanglement: the Coffman–Kundu–Wootters inequality

A pure state of three qubits `A`, `B`, `C` is described by its amplitudes
`a i j k` (`i` the `A`-index, `j` the `B`-index, `k` the `C`-index) in the
computational basis, i.e. `|ψ⟩ = ∑ a i j k • |i j k⟩`.

* `QI.rhoA a` is the reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|`;
* `QI.tauA a = 4 det ρ_A` is the tangle of the bipartite cut `A | BC`
  (for a normalised state this equals `2 (1 - Tr ρ_A²)`, the squared
  concurrence of the pure bipartite state; see `QI.tauA_eq_two_mul_one_sub_purity`);
* `QI.Mab a` is the `2 × 2` matrix `M` of the "spin flip" bilinear form
  `⟨φ_k| σ_y ⊗ σ_y |φ_l^*⟩` built from the (unnormalised) conditional vectors
  `φ_k = ∑_{ij} a i j k • |ij⟩` on `AB` obtained by tracing out `C`.  The singular
  values `σ₁ ≥ σ₂` of `M` are exactly the square roots of the eigenvalues of
  `ρ_{AB} ρ̃_{AB}` occurring in Wootters' formula, so the squared concurrence of
  `ρ_{AB}` is `C²_{AB} = (σ₁ - σ₂)² = σ₁² + σ₂² - 2 σ₁σ₂ = ‖M‖_F² - 2 |det M|`,
  which is `QI.CABsq a`;
* symmetrically `QI.Mac a` and `QI.CACsq a` for the pair `A C`.

The main theorem `QI.monogamy_ckw` is the CKW inequality
`C²_{AB} + C²_{AC} ≤ τ_{A|BC}`.

The heart of the matter is the polynomial identity `QI.tauA_eq_frob_add_frob`,
`τ_{A|BC} = ‖M‖_F² + ‖N‖_F²`, after which monogamy follows from `|det M| ≥ 0`
and `|det N| ≥ 0`.  The deficit is exactly `2 (|det M| + |det N|)`, twice the
residual three-way entanglement (`QI.monogamy_ckw_deficit`).

All statements are homogeneous of degree `4` in the amplitudes, so no
normalisation hypothesis is needed.
-/

namespace QI

open Complex Finset Matrix

noncomputable section

variable (a : Fin 2 → Fin 2 → Fin 2 → ℂ)

/-- The reduced density matrix of qubit `A` for the three-qubit pure state with
amplitudes `a`. -/
def rhoA : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j : Fin 2, ∑ k : Fin 2, a i j k * (starRingEnd ℂ) (a i' j k)

/-- The tangle of the bipartite cut `A | BC`, i.e. `4 det ρ_A`. -/
def tauA : ℝ := 4 * ((rhoA a).det).re

/-- The `2 × 2` matrix whose singular values are the square roots of the
eigenvalues of `ρ_{AB} ρ̃_{AB}` (Wootters' matrix for the pair `A B`). -/
def Mab : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun k l => a 0 0 k * a 1 1 l + a 1 1 k * a 0 0 l - a 0 1 k * a 1 0 l - a 1 0 k * a 0 1 l

/-- The `2 × 2` matrix whose singular values are the square roots of the
eigenvalues of `ρ_{AC} ρ̃_{AC}` (Wootters' matrix for the pair `A C`). -/
def Mac : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j l => a 0 j 0 * a 1 l 1 + a 1 j 1 * a 0 l 0 - a 0 j 1 * a 1 l 0 - a 1 j 0 * a 0 l 1

/-- The squared Frobenius norm of a `2 × 2` complex matrix. -/
def frob (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ k : Fin 2, ∑ l : Fin 2, normSq (M k l)

/-- Wootters' squared concurrence attached to a `2 × 2` matrix `M` with singular
values `σ₁ ≥ σ₂`: it equals `(σ₁ - σ₂)² = ‖M‖_F² - 2 |det M|`. -/
def concSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := frob M - 2 * ‖M.det‖

/-- The squared concurrence of the two-qubit mixed state `ρ_{AB}`. -/
def CABsq : ℝ := concSq (Mab a)

/-- The squared concurrence of the two-qubit mixed state `ρ_{AC}`. -/
def CACsq : ℝ := concSq (Mac a)

/-! ### Basic sanity lemmas -/

/-- `ρ_A` is Hermitian. -/
lemma rhoA_isHermitian : (rhoA a).IsHermitian := by
  ext i i'
  simp only [rhoA, Matrix.conjTranspose_apply, Matrix.of_apply, star_def, map_sum, map_mul,
    Complex.conj_conj]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The determinant of `ρ_A` is a real number, so `tauA` really is `4 det ρ_A`. -/
lemma rhoA_det_im : ((rhoA a).det).im = 0 := by
  simp only [rhoA, Matrix.det_fin_two, Matrix.of_apply, Fin.sum_univ_two, Complex.sub_im,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

lemma tauA_ofReal : ((tauA a : ℝ) : ℂ) = 4 * (rhoA a).det := by
  have h := rhoA_det_im a
  rw [Complex.ext_iff]
  refine ⟨by simp [tauA, Complex.mul_re], by simp [tauA, Complex.mul_im, h]⟩

/-- For a normalised state, the trace of `ρ_A` is one. -/
lemma rhoA_trace_eq_one
    (hnorm : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, normSq (a i j k) = 1) :
    (rhoA a).trace = 1 := by
  have h : (rhoA a).trace = ((∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, normSq (a i j k) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, rhoA, Matrix.of_apply, Fin.sum_univ_two,
      Complex.ofReal_add, ← Complex.mul_conj]
  rw [h, hnorm]
  norm_num

/-- For a normalised state, the tangle of the cut `A|BC` is `2 (1 - Tr ρ_A²)`,
i.e. the squared concurrence of the bipartite pure state across that cut. -/
lemma tauA_eq_two_mul_one_sub_purity
    (hnorm : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, normSq (a i j k) = 1) :
    tauA a = 2 * (1 - ((rhoA a * rhoA a).trace).re) := by
  have htr := rhoA_trace_eq_one a hnorm
  have hsq : (rhoA a * rhoA a).trace = (rhoA a).trace ^ 2 - 2 * (rhoA a).det := by
    simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hsq, htr]
  simp only [tauA, one_pow, Complex.sub_re, Complex.one_re, Complex.mul_re]
  norm_num
  ring

/-! ### The key polynomial identity -/

set_option maxHeartbeats 1000000 in
/-- **Key identity.**  The tangle of the cut `A|BC` is the sum of the squared
Frobenius norms of the two Wootters matrices. -/
lemma tauA_eq_frob_add_frob : tauA a = frob (Mab a) + frob (Mac a) := by
  have key : (4 : ℂ) * (rhoA a).det = ((frob (Mab a) + frob (Mac a) : ℝ) : ℂ) := by
    simp only [frob, Fin.sum_univ_two, Complex.ofReal_add, ← Complex.mul_conj, rhoA, Mab, Mac,
      Matrix.det_fin_two, Matrix.of_apply, map_add, map_sub, map_mul]
    ring
  have h : ((tauA a : ℝ) : ℂ) = ((frob (Mab a) + frob (Mac a) : ℝ) : ℂ) := by
    rw [tauA_ofReal a, key]
  exact_mod_cast h

/-! ### Positivity of the Wootters concurrence -/

/-- For a `2 × 2` matrix, `2 |det M| ≤ ‖M‖_F²`; equivalently the Wootters
squared concurrence `(σ₁ - σ₂)²` is nonnegative. -/
lemma two_mul_norm_det_le_frob (M : Matrix (Fin 2) (Fin 2) ℂ) : 2 * ‖M.det‖ ≤ frob M := by
  have hdet : ‖M.det‖ ≤ ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by
    rw [Matrix.det_fin_two]
    calc ‖M 0 0 * M 1 1 - M 0 1 * M 1 0‖ ≤ ‖M 0 0 * M 1 1‖ + ‖M 0 1 * M 1 0‖ := norm_sub_le _ _
      _ = ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by rw [norm_mul, norm_mul]
  have hf : frob M = ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2 := by
    simp only [frob, Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
    ring
  nlinarith [sq_nonneg (‖M 0 0‖ - ‖M 1 1‖), sq_nonneg (‖M 0 1‖ - ‖M 1 0‖)]

lemma concSq_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ concSq M := by
  have := two_mul_norm_det_le_frob M
  simp only [concSq]
  linarith

lemma concSq_le_frob (M : Matrix (Fin 2) (Fin 2) ℂ) : concSq M ≤ frob M := by
  have h : (0 : ℝ) ≤ ‖M.det‖ := norm_nonneg _
  simp only [concSq]
  linarith

/-! ### The CKW monogamy inequality -/

/-- **Monogamy of entanglement (Coffman–Kundu–Wootters).**
For any pure state of three qubits, the squared concurrences of the two-qubit
marginals `ρ_{AB}` and `ρ_{AC}` satisfy `C²_{AB} + C²_{AC} ≤ τ_{A|BC}`, where
`τ_{A|BC} = 4 det ρ_A` is the tangle of the bipartite cut separating `A` from
`BC`. -/
theorem monogamy_ckw : CABsq a + CACsq a ≤ tauA a := by
  rw [tauA_eq_frob_add_frob]
  exact add_le_add (concSq_le_frob _) (concSq_le_frob _)

/-- A sharper form: the deficit in the CKW inequality is exactly
`2 (|det M| + |det N|) ≥ 0`, the residual three-way entanglement. -/
theorem monogamy_ckw_deficit :
    tauA a - (CABsq a + CACsq a) = 2 * (‖(Mab a).det‖ + ‖(Mac a).det‖) := by
  rw [tauA_eq_frob_add_frob]
  simp only [CABsq, CACsq, concSq]
  ring

/-- Both squared concurrences are nonnegative. -/
theorem CABsq_nonneg : 0 ≤ CABsq a := concSq_nonneg _

theorem CACsq_nonneg : 0 ≤ CACsq a := concSq_nonneg _

/-! ### Two examples: the GHZ and W states

Both are written with unnormalised amplitudes; all quantities are homogeneous of
degree `4`, so this only rescales them by a common positive factor. -/

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
def ghz : Fin 2 → Fin 2 → Fin 2 → ℂ := ![![![1, 0], ![0, 0]], ![![0, 0], ![0, 1]]]

/-- The (unnormalised) W state `|001⟩ + |010⟩ + |100⟩`. -/
def wState : Fin 2 → Fin 2 → Fin 2 → ℂ := ![![![0, 1], ![1, 0]], ![![1, 0], ![0, 0]]]

/-- For the GHZ state all two-qubit concurrences vanish while the tangle of the
cut `A|BC` is maximal: the CKW inequality is strict, the whole entanglement
being three-way. -/
theorem ghz_values : tauA ghz = 4 ∧ CABsq ghz = 0 ∧ CACsq ghz = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · norm_num [tauA, CABsq, CACsq, concSq, frob, rhoA, Mab, Mac, ghz, Matrix.det_fin_two,
      Fin.sum_univ_two, Complex.normSq_apply]

/-- For the W state the CKW inequality is an equality, so the bound is sharp. -/
theorem wState_values : tauA wState = 8 ∧ CABsq wState = 4 ∧ CACsq wState = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · norm_num [tauA, CABsq, CACsq, concSq, frob, rhoA, Mab, Mac, wState, Matrix.det_fin_two,
      Fin.sum_univ_two, Complex.normSq_apply]

/-- The CKW bound is attained: for the W state `C²_{AB} + C²_{AC} = τ_{A|BC}`. -/
theorem monogamy_ckw_sharp : CABsq wState + CACsq wState = tauA wState := by
  obtain ⟨h1, h2, h3⟩ := wState_values
  rw [h1, h2, h3]
  norm_num

/-- The tangle of the cut `A|BC` is nonnegative. -/
theorem tauA_nonneg : 0 ≤ tauA a := by
  rw [tauA_eq_frob_add_frob]
  have h1 : (0 : ℝ) ≤ frob (Mab a) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _
  have h2 : (0 : ℝ) ≤ frob (Mac a) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _
  linarith

end

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

