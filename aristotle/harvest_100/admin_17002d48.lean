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

/-
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We work with finite-dimensional quantum systems, i.e. complex matrices `Matrix n n ℂ`.

* `QI.Channel ι n m` is a CPTP map (quantum channel) given in Kraus form: a family of Kraus
  operators `K i : Matrix m n ℂ` with `∑ i, (K i)ᴴ * K i = 1`.  `QI.Channel.map` is the
  Schrödinger picture action `X ↦ ∑ i, K i * X * (K i)ᴴ`; it is proved to be positive
  (`QI.Channel.map_posSemidef`) and trace preserving (`QI.Channel.trace_map`).
* `QI.posPartTrace X` is the trace of the positive part of a Hermitian matrix, defined
  variationally as `sup { Re Tr (X P) : 0 ≤ P ≤ 1 }` and valued in `ℝ≥0∞`.  Theorem
  `QI.posPartTrace_eq_sum_eigenvalues` identifies it with `∑ᵢ (λᵢ)₊`, the usual
  `Tr X₊`, for Hermitian `X`.
* `QI.posPartTrace_map_le` is the data processing inequality for the hockey-stick
  divergence: `Tr (Φ(X))₊ ≤ Tr X₊` for every channel `Φ`.
* `QI.relEntropy ρ σ` is the quantum relative entropy, expressed through Frenkel's integral
  formula
  `D(ρ ‖ σ) = ∫_0^∞ (Tr (ρ - tσ)₊ - (Tr ρ) (1 - t)₊) dt / t`,
  written as a lower Lebesgue integral (so its value lies in `ℝ≥0∞`, with `∞` allowed).
* `QI.data_processing` is the **data processing inequality**: `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`
  for every channel `Φ` and all `ρ`, `σ`.

## Remarks on the definition of relative entropy

That the integral formula above computes `Tr ρ (log ρ - log σ)` for arbitrary (in particular
non-commuting) density matrices is a theorem of P. E. Frenkel, *Integral formula for quantum
relative entropy implies data processing inequality*, J. Phys. A **56** (2023) 385303;
that identification is *not* formalised here.  What is formalised, besides the data processing
inequality itself, are the following consistency results:

* `QI.relEntropy_diagonal` (in `RequestProject.ClassicalCase`): for commuting states, i.e. for
  diagonal density matrices with entries given by probability vectors `p`, `q` with `q > 0`,
  the formula returns the classical Kullback-Leibler divergence `∑ᵢ pᵢ log (pᵢ / qᵢ)`.
* `QI.relEntropy_self`: `D(ρ ‖ ρ) = 0`.
* `QI.relEntropy_conj_unitary`: invariance under simultaneous unitary conjugation.

The data processing inequality proved here is in fact slightly stronger than the standard
statement in two ways: the integrand inequality only uses that the dual of the channel maps
effects to effects, and the states `ρ`, `σ` are arbitrary matrices.
-/

open scoped ENNReal ComplexOrder
open Matrix MeasureTheory

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- An *effect* (or *test operator*) is a matrix `P` with `0 ≤ P ≤ 1`. -/
def IsEffect (P : Matrix n n ℂ) : Prop := P.PosSemidef ∧ (1 - P).PosSemidef

/-- The trace of the positive part of a Hermitian matrix, in variational form:
`Tr X₊ = sup { Re Tr (X P) : 0 ≤ P ≤ 1 }`. -/
noncomputable def posPartTrace (X : Matrix n n ℂ) : ℝ≥0∞ :=
  ⨆ P : {P : Matrix n n ℂ // IsEffect P}, ENNReal.ofReal (X * (P : Matrix n n ℂ)).trace.re

/-- A quantum channel (CPTP map) in Kraus form. -/
structure Channel (ι : Type*) [Fintype ι] (n m : Type*) [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] where
  K : ι → Matrix m n ℂ
  tp : ∑ i, (K i)ᴴ * K i = 1

namespace Channel

variable (Φ : Channel ι n m)

/-- The action of the channel (Schrödinger picture). -/
noncomputable def map (X : Matrix n n ℂ) : Matrix m m ℂ := ∑ i, Φ.K i * X * (Φ.K i)ᴴ

/-- The adjoint (Heisenberg picture) of the channel. -/
noncomputable def dual (Y : Matrix m m ℂ) : Matrix n n ℂ := ∑ i, (Φ.K i)ᴴ * Y * Φ.K i

/-- A channel is a positive map. -/
lemma map_posSemidef {X : Matrix n n ℂ} (hX : X.PosSemidef) : (Φ.map X).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => hX.mul_mul_conjTranspose_same _

/-- A channel is trace preserving. -/
lemma trace_map (X : Matrix n n ℂ) : (Φ.map X).trace = X.trace := by
  rw [Channel.map, Matrix.trace_sum]
  simp only [Matrix.trace_mul_cycle (Φ.K _) X ((Φ.K _)ᴴ)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, Φ.tp, one_mul]

lemma map_sub (X Y : Matrix n n ℂ) : Φ.map (X - Y) = Φ.map X - Φ.map Y := by
  simp [Channel.map, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

lemma map_smul (c : ℂ) (X : Matrix n n ℂ) : Φ.map (c • X) = c • Φ.map X := by
  simp [Channel.map, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The dual map is unital. -/
lemma dual_one : Φ.dual 1 = 1 := by
  simp [Channel.dual, Φ.tp]

lemma dual_posSemidef {Y : Matrix m m ℂ} (hY : Y.PosSemidef) : (Φ.dual Y).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => hY.conjTranspose_mul_mul_same _

lemma dual_sub (Y Z : Matrix m m ℂ) : Φ.dual (Y - Z) = Φ.dual Y - Φ.dual Z := by
  simp [Channel.dual, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

/-- The dual map sends effects to effects. -/
lemma dual_isEffect {P : Matrix m m ℂ} (hP : IsEffect P) : IsEffect (Φ.dual P) := by
  refine ⟨Φ.dual_posSemidef hP.1, ?_⟩
  rw [← Φ.dual_one, ← Φ.dual_sub]
  exact Φ.dual_posSemidef hP.2

/-- The defining property of the dual map: `Tr (Φ(X) P) = Tr (X Φ*(P))`. -/
lemma trace_map_mul (X : Matrix n n ℂ) (P : Matrix m m ℂ) :
    (Φ.map X * P).trace = (X * Φ.dual P).trace := by
  rw [Channel.map, Channel.dual, Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : Φ.K i * X * (Φ.K i)ᴴ * P = Φ.K i * (X * (Φ.K i)ᴴ * P) := by simp [Matrix.mul_assoc]
  have h2 : X * ((Φ.K i)ᴴ * P * Φ.K i) = X * (Φ.K i)ᴴ * P * Φ.K i := by simp [Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm]

end Channel

/-- Data processing for the hockey-stick functional `Tr (·)₊`: for every channel `Φ` and every
matrix `X`, `Tr (Φ(X))₊ ≤ Tr X₊`.  This is immediate from the variational description, since the
dual map sends effects to effects. -/
lemma posPartTrace_map_le (Φ : Channel ι n m) (X : Matrix n n ℂ) :
    posPartTrace (Φ.map X) ≤ posPartTrace X := by
  refine iSup_le fun P => ?_
  rw [Φ.trace_map_mul X P.1]
  exact le_iSup (fun Q : {Q : Matrix n n ℂ // IsEffect Q} =>
    ENNReal.ofReal (X * (Q : Matrix n n ℂ)).trace.re) ⟨Φ.dual P.1, Φ.dual_isEffect P.2⟩

/-!
### `posPartTrace` really is the trace of the positive part

We check that the variational quantity `posPartTrace` agrees with `Tr X₊ = ∑ᵢ (λᵢ)₊`, the sum
of the positive parts of the eigenvalues of a Hermitian matrix `X`.
-/

omit [Fintype n] in
/-- Diagonal entries of an effect lie in `[0, 1]`. -/
lemma IsEffect.diag_mem_Icc {P : Matrix n n ℂ} (hP : IsEffect P) (i : n) :
    0 ≤ (P i i).re ∧ (P i i).re ≤ 1 := by
  have h1 : (0 : ℂ) ≤ P i i := hP.1.diag_nonneg
  have h2 : (0 : ℂ) ≤ (1 - P) i i := hP.2.diag_nonneg
  simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h2
  refine ⟨(Complex.le_def.mp h1).1, ?_⟩
  have := (Complex.le_def.mp h2).1
  simp at this
  linarith

/-- For a real diagonal matrix, `posPartTrace` is the sum of the positive parts of the entries. -/
theorem posPartTrace_diagonal (d : n → ℝ) :
    posPartTrace (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) =
      ENNReal.ofReal (∑ i, max (d i) 0) := by
  apply le_antisymm
  · refine iSup_le fun P => ?_
    have hentry := fun i => P.2.diag_mem_Icc i
    have htr : (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (P : Matrix n n ℂ)).trace.re
        = ∑ i, d i * ((P : Matrix n n ℂ) i i).re := by
      simp [Matrix.trace, Matrix.diagonal_mul, Matrix.diag, Complex.re_sum]
    rw [htr]
    apply ENNReal.ofReal_le_ofReal
    refine Finset.sum_le_sum fun i _ => ?_
    rcases le_or_gt 0 (d i) with h | h
    · calc d i * ((P : Matrix n n ℂ) i i).re ≤ d i * 1 :=
            mul_le_mul_of_nonneg_left (hentry i).2 h
        _ = d i := by ring
        _ ≤ max (d i) 0 := le_max_left _ _
    · exact (mul_nonpos_of_nonpos_of_nonneg h.le (hentry i).1).trans (le_max_right _ _)
  · set e : n → ℂ := fun i => if 0 ≤ d i then 1 else 0 with he
    have hsub : (1 : Matrix n n ℂ) - Matrix.diagonal e = Matrix.diagonal (fun i => 1 - e i) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    have hP : IsEffect (Matrix.diagonal e) := by
      refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
      · intro i; simp only [he]; split <;> simp
      · rw [hsub]
        refine Matrix.PosSemidef.diagonal ?_
        intro i; simp only [he]; split <;> simp
    have hle := le_iSup (fun Q : {Q : Matrix n n ℂ // IsEffect Q} =>
      ENNReal.ofReal (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * (Q : Matrix n n ℂ)).trace.re)
      ⟨Matrix.diagonal e, hP⟩
    refine le_trans (le_of_eq ?_) hle
    congr 1
    simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, he]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 0 ≤ d i
    · simp [h]
    · have h' : d i ≤ 0 := le_of_lt (not_le.mp h)
      simp [h, max_eq_right h']

/-- The unitary channel `X ↦ U X Uᴴ`. -/
noncomputable def unitaryChannel {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) : Channel Unit n n where
  K := fun _ => U
  tp := by simpa using hU

@[simp] lemma unitaryChannel_map {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (X : Matrix n n ℂ) :
    (unitaryChannel hU).map X = U * X * Uᴴ := by
  simp [Channel.map, unitaryChannel]

/-- `posPartTrace` is invariant under unitary conjugation. -/
lemma posPartTrace_conj_unitary {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (X : Matrix n n ℂ) :
    posPartTrace (U * X * Uᴴ) = posPartTrace X := by
  have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa [Matrix.conjTranspose_conjTranspose] using mul_eq_one_comm.mp hU
  refine le_antisymm ?_ ?_
  · rw [← unitaryChannel_map hU X]
    exact posPartTrace_map_le _ _
  · have hX : X = Uᴴ * (U * X * Uᴴ) * (Uᴴ)ᴴ := by
      simp only [Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, ← Matrix.mul_assoc, hU,
        Matrix.one_mul]
    conv_lhs => rw [hX, ← unitaryChannel_map hUU (U * X * Uᴴ)]
    exact posPartTrace_map_le _ _

/-- **`posPartTrace` is the trace of the positive part**: for a Hermitian matrix `X` with
eigenvalues `λᵢ`, the variational quantity `sup { Re Tr (X P) : 0 ≤ P ≤ 1 }` equals `∑ᵢ (λᵢ)₊`. -/
theorem posPartTrace_eq_sum_eigenvalues {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    posPartTrace X = ENNReal.ofReal (∑ i, max (hX.eigenvalues i) 0) := by
  have hU : ((hX.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hX.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self hX.eigenvectorUnitary)
  have hspec : X = (hX.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [Matrix.star_eq_conjTranspose, Function.comp_def]
  conv_lhs => rw [hspec]
  rw [posPartTrace_conj_unitary hU, posPartTrace_diagonal]

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
lemma trace_mul_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have hAh : A.IsHermitian := hA.isHermitian
  set U : Matrix n n ℂ := (hAh.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => ((hAh.eigenvalues i : ℝ) : ℂ)) with hD
  have hspec : A = U * D * Uᴴ := by
    conv_lhs => rw [hAh.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [Matrix.star_eq_conjTranspose, Function.comp_def, hUdef, hD]
  have hC : (Uᴴ * B * U).PosSemidef := hB.conjTranspose_mul_mul_same U
  have hcyc : (A * B).trace = (D * (Uᴴ * B * U)).trace := by
    conv_lhs => rw [hspec]
    rw [show U * D * Uᴴ * B = U * (D * (Uᴴ * B)) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [hcyc, Matrix.trace]
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 : (0 : ℝ) ≤ hAh.eigenvalues i := hA.eigenvalues_nonneg i
  have h2 : (0 : ℂ) ≤ (Uᴴ * B * U) i i := hC.diag_nonneg
  have hdd : (D * (Uᴴ * B * U)).diag i = ((hAh.eigenvalues i : ℝ) : ℂ) * (Uᴴ * B * U) i i := by
    simp [Matrix.diag, hD, Matrix.diagonal_mul]
  rw [hdd]
  exact mul_nonneg (by simpa using Complex.zero_le_real.mpr h1) h2

omit [Fintype n] in
/-- `1` is an effect. -/
lemma isEffect_one : IsEffect (1 : Matrix n n ℂ) :=
  ⟨Matrix.PosSemidef.one, by simpa using Matrix.PosSemidef.zero⟩

/-- For a nonnegative multiple of a positive semidefinite matrix, `posPartTrace` is the trace
(and it vanishes for negative multiples). -/
lemma posPartTrace_smul_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) (c : ℝ) :
    posPartTrace ((c : ℂ) • A) = ENNReal.ofReal (c * A.trace.re) := by
  have hTr : (0 : ℝ) ≤ A.trace.re := (Complex.le_def.mp hA.trace_nonneg).1
  apply le_antisymm
  · refine iSup_le fun P => ?_
    have hmul : (((c : ℂ) • A) * (P : Matrix n n ℂ)).trace.re
        = c * (A * (P : Matrix n n ℂ)).trace.re := by
      rw [Matrix.smul_mul, Matrix.trace_smul]
      simp
    have h0 : 0 ≤ (A * (P : Matrix n n ℂ)).trace.re :=
      (Complex.le_def.mp (trace_mul_nonneg hA P.2.1)).1
    have h1 : (A * (P : Matrix n n ℂ)).trace.re ≤ A.trace.re := by
      have := (Complex.le_def.mp (trace_mul_nonneg hA P.2.2)).1
      rw [Matrix.mul_sub, Matrix.trace_sub] at this
      simp only [Matrix.mul_one, Complex.sub_re, Complex.zero_re] at this
      linarith
    rw [hmul]
    rcases le_or_gt 0 c with hc | hc
    · exact ENNReal.ofReal_le_ofReal (by nlinarith)
    · have : c * (A * (P : Matrix n n ℂ)).trace.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le h0
      simp [ENNReal.ofReal_eq_zero.mpr this]
  · rcases le_or_gt 0 c with hc | hc
    · have hle := le_iSup (fun Q : {Q : Matrix n n ℂ // IsEffect Q} =>
        ENNReal.ofReal ((((c : ℂ) • A) * (Q : Matrix n n ℂ)).trace.re)) ⟨1, isEffect_one⟩
      refine le_trans (le_of_eq ?_) hle
      congr 1
      simp
    · have : c * A.trace.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hTr
      simp [ENNReal.ofReal_eq_zero.mpr this]

/-- Quantum relative entropy, via Frenkel's integral formula. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ),
    (posPartTrace (ρ - (t : ℂ) • σ) - ENNReal.ofReal (ρ.trace.re * max 0 (1 - t)))
      / ENNReal.ofReal t

/-- **Data processing inequality**: quantum relative entropy is monotone under CPTP maps. -/
theorem data_processing (Φ : Channel ι n m) (ρ σ : Matrix n n ℂ) :
    relEntropy (Φ.map ρ) (Φ.map σ) ≤ relEntropy ρ σ := by
  refine lintegral_mono fun t => ?_
  have hmap : Φ.map ρ - (t : ℂ) • Φ.map σ = Φ.map (ρ - (t : ℂ) • σ) := by
    rw [Φ.map_sub, Φ.map_smul]
  have htr : (Φ.map ρ).trace.re = ρ.trace.re := by rw [Φ.trace_map]
  rw [hmap, htr]
  gcongr
  exact posPartTrace_map_le Φ _

/-- The relative entropy of a state with itself vanishes. -/
theorem relEntropy_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : relEntropy ρ ρ = 0 := by
  have hTr : (0 : ℝ) ≤ ρ.trace.re := (Complex.le_def.mp hρ.trace_nonneg).1
  have hzero : ∀ t ∈ Set.Ioi (0 : ℝ),
      (posPartTrace (ρ - (t : ℂ) • ρ) - ENNReal.ofReal (ρ.trace.re * max 0 (1 - t)))
        / ENNReal.ofReal t = 0 := by
    intro t _
    have hsmul : ρ - (t : ℂ) • ρ = (((1 - t : ℝ)) : ℂ) • ρ := by
      push_cast
      module
    rw [hsmul, posPartTrace_smul_posSemidef hρ]
    have : ENNReal.ofReal ((1 - t) * ρ.trace.re) = ENNReal.ofReal (ρ.trace.re * max 0 (1 - t)) := by
      rcases le_total t 1 with h | h
      · rw [max_eq_right (by linarith)]
        ring_nf
      · rw [max_eq_left (by linarith), mul_zero, ENNReal.ofReal_zero,
          ENNReal.ofReal_eq_zero.mpr (by nlinarith)]
    rw [this, tsub_self, ENNReal.zero_div]
  rw [relEntropy, setLIntegral_congr_fun measurableSet_Ioi hzero, lintegral_zero]

/-- Relative entropy is invariant under conjugating both arguments by a unitary. -/
theorem relEntropy_conj_unitary {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (ρ σ : Matrix n n ℂ) :
    relEntropy (U * ρ * Uᴴ) (U * σ * Uᴴ) = relEntropy ρ σ := by
  have htr : (U * ρ * Uᴴ).trace = ρ.trace := by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  refine lintegral_congr fun t => ?_
  have hsub : U * ρ * Uᴴ - (t : ℂ) • (U * σ * Uᴴ) = U * (ρ - (t : ℂ) • σ) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsub, posPartTrace_conj_unitary hU, htr]

end QI

import RequestProject.DataProcessing

/-!
# The commuting (classical) case of Frenkel's integral formula

This file checks that the integral formula used to define `QI.relEntropy` reproduces the
textbook expression for the relative entropy of *commuting* states, i.e. the classical
Kullback-Leibler divergence
`D(p ‖ q) = ∑ᵢ pᵢ log (pᵢ / qᵢ)`
of two probability vectors.  For general (non-commuting) density matrices the same integral
formula still computes `Tr ρ (log ρ - log σ)`; that is Frenkel's theorem
(P. E. Frenkel, *Integral formula for quantum relative entropy implies data processing
inequality*, J. Phys. A 56 (2023)), which is not formalised here.
-/

open MeasureTheory Set intervalIntegral
open scoped ENNReal ComplexOrder

namespace QI

/-- The scalar integrand of Frenkel's formula:
`((p - t q)₊ - p (1 - t)₊) / t = (min p (t p) - min p (t q)) / t`. -/
noncomputable def fren (p q t : ℝ) : ℝ := (min p (t * p) - min p (t * q)) / t

lemma fren_eq_posPart (p q t : ℝ) (hp : 0 ≤ p) :
    fren p q t = (max (p - t * q) 0 - p * max (1 - t) 0) / t := by
  have h1 : max (p - t * q) 0 = p - min p (t * q) := by
    rcases le_total (t * q) p with h | h
    · rw [min_eq_right h, max_eq_left (by linarith)]
    · rw [min_eq_left h, max_eq_right (by linarith)]
      ring
  have h2 : p * max (1 - t) 0 = p - min p (t * p) := by
    rcases le_total t 1 with h | h
    · rw [max_eq_left (by linarith), min_eq_right (by nlinarith)]
      ring
    · rw [max_eq_right (by linarith), min_eq_left (by nlinarith)]
      ring
  rw [fren, h1, h2]
  ring_nf

lemma fren_bound (p q : ℝ) {t : ℝ} (ht : 0 < t) : |fren p q t| ≤ |p - q| := by
  have h := abs_min_sub_min_le_max p (t * p) p (t * q)
  simp only [sub_self, abs_zero] at h
  rw [max_eq_right (abs_nonneg _)] at h
  rw [fren, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  calc |min p (t * p) - min p (t * q)| ≤ |t * p - t * q| := h
    _ = t * |p - q| := by rw [← mul_sub, abs_mul, abs_of_pos ht]
    _ = |p - q| * t := by ring

lemma measurable_fren (p q : ℝ) : Measurable (fren p q) := by unfold fren; fun_prop

lemma fren_eq_zero (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) {t : ℝ} (ht : max 1 (p / q) ≤ t) :
    fren p q t = 0 := by
  have h1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have h2 : p / q ≤ t := le_trans (le_max_right _ _) ht
  have hp1 : min p (t * p) = p := min_eq_left (by nlinarith)
  have hp2 : min p (t * q) = p := min_eq_left (by rw [div_le_iff₀ hq] at h2; nlinarith)
  simp [fren, hp1, hp2]

lemma fren_small (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) {t : ℝ} (ht : 0 < t)
    (h1 : t ≤ 1) (h2 : t ≤ p / q) : fren p q t = p - q := by
  have e1 : min p (t * p) = t * p := min_eq_right (by nlinarith)
  have e2 : min p (t * q) = t * q := min_eq_right (by rw [le_div_iff₀ hq] at h2; nlinarith)
  rw [fren, e1, e2]
  field_simp

lemma fren_mid1 (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) {t : ℝ} (ht : 0 < t)
    (h1 : t ≤ 1) (h2 : p / q ≤ t) : fren p q t = p - p * t⁻¹ := by
  have e1 : min p (t * p) = t * p := min_eq_right (by nlinarith)
  have e2 : min p (t * q) = p := min_eq_left (by rw [div_le_iff₀ hq] at h2; nlinarith)
  rw [fren, e1, e2]
  field_simp

lemma fren_mid2 (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) {t : ℝ} (ht : 0 < t)
    (h1 : 1 ≤ t) (h2 : t ≤ p / q) : fren p q t = p * t⁻¹ - q := by
  have e1 : min p (t * p) = p := min_eq_left (by nlinarith)
  have e2 : min p (t * q) = t * q := min_eq_right (by rw [le_div_iff₀ hq] at h2; nlinarith)
  rw [fren, e1, e2]
  field_simp

lemma integrableOn_fren (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    IntegrableOn (fren p q) (Ioi 0) := by
  set B := max 1 (p / q) with hB
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one (le_max_left _ _)
  have h1 : IntegrableOn (fren p q) (Ioc 0 B) := by
    refine Measure.integrableOn_of_bounded (M := |p - q|) measure_Ioc_lt_top.ne
      (measurable_fren p q).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa [Real.norm_eq_abs] using fren_bound p q ht.1
  have heq : EqOn (0 : ℝ → ℝ) (fren p q) (Ioi B) :=
    fun t ht => (fren_eq_zero p q hp hq (le_of_lt ht)).symm
  have h2 : IntegrableOn (fren p q) (Ioi B) :=
    integrableOn_zero.congr_fun heq measurableSet_Ioi
  rw [show Ioi (0 : ℝ) = Ioc 0 B ∪ Ioi B from (Ioc_union_Ioi_eq_Ioi hB0).symm]
  exact h1.union h2

lemma integral_Ioi_of_eventually_zero {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {B : ℝ} (hB : 0 ≤ B) (hzero : ∀ t, B ≤ t → f t = 0) :
    ∫ t in Ioi (0 : ℝ), f t = ∫ t in (0 : ℝ)..B, f t := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 B ∪ Ioi B := (Ioc_union_Ioi_eq_Ioi hB).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) B) (Ioi B) := Ioc_disjoint_Ioi_same
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi
    (hf.mono_set (by rw [hsplit]; exact subset_union_left))
    (hf.mono_set (by rw [hsplit]; exact subset_union_right))]
  have hz : ∫ t in Ioi B, f t = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun t ht => hzero t (le_of_lt ht))]
    simp
  rw [hz, add_zero, intervalIntegral.integral_of_le hB]

/-- **Frenkel's scalar integral**: `∫₀^∞ ((p - t q)₊ - p (1 - t)₊) dt / t = p log (p / q)`. -/
theorem integral_fren (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    ∫ t in Ioi (0 : ℝ), fren p q t = p * Real.log (p / q) := by
  rcases hp.eq_or_lt with hp0 | hp0
  · have hpz : p = 0 := hp0.symm
    have hz : ∀ t ∈ Ioi (0 : ℝ), fren p q t = 0 := by
      intro t ht
      have h1 : min p (t * p) = 0 := by simp [hpz]
      have h2 : min p (t * q) = 0 := by
        rw [hpz]; exact min_eq_left (le_of_lt (mul_pos ht hq))
      rw [fren, h1, h2]; simp
    rw [setIntegral_congr_fun measurableSet_Ioi hz]
    simp [hpz]
  · set a := p / q with ha
    have ha0 : 0 < a := div_pos hp0 hq
    have haq : a * q = p := div_mul_cancel₀ p (ne_of_gt hq)
    have hint := integrableOn_fren p q hp hq
    have hB0 : (0 : ℝ) ≤ max 1 a := le_trans zero_le_one (le_max_left _ _)
    have hmain := integral_Ioi_of_eventually_zero hint hB0
      (fun t ht => fren_eq_zero p q hp hq ht)
    have hii : ∀ x y : ℝ, 0 ≤ x → x ≤ y → IntervalIntegrable (fren p q) volume x y := by
      intro x y hx hxy
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
      exact hint.mono_set (fun t ht => lt_of_le_of_lt hx ht.1)
    rcases le_total a 1 with hle | hle
    · rw [max_eq_left hle] at hmain
      rw [hmain, ← intervalIntegral.integral_add_adjacent_intervals
        (hii 0 a (le_refl 0) ha0.le) (hii a 1 ha0.le hle)]
      have e1 : ∫ t in (0 : ℝ)..a, fren p q t = ∫ _t in (0 : ℝ)..a, (p - q) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
        rw [Set.uIoc_of_le ha0.le] at ht
        exact fren_small p q hp hq ht.1 (le_trans ht.2 hle) ht.2
      have e2 : ∫ t in a..(1 : ℝ), fren p q t = ∫ t in a..(1 : ℝ), (p - p * t⁻¹) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hle] at ht
        exact fren_mid1 p q hp hq (lt_of_lt_of_le ha0 ht.1) ht.2 ht.1
      have h1 : IntervalIntegrable (fun t : ℝ => p * t⁻¹) volume a 1 := by
        refine (ContinuousOn.mul continuousOn_const
          (ContinuousOn.inv₀ continuousOn_id ?_)).intervalIntegrable
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
      rw [e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const h1,
        intervalIntegral.integral_const, intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 zero_lt_one,
        one_div, Real.log_inv]
      simp only [smul_eq_mul, sub_zero]
      nlinarith [haq]
    · rw [max_eq_right hle] at hmain
      rw [hmain, ← intervalIntegral.integral_add_adjacent_intervals
        (hii 0 1 (le_refl 0) zero_le_one) (hii 1 a zero_le_one hle)]
      have e1 : ∫ t in (0 : ℝ)..1, fren p q t = ∫ _t in (0 : ℝ)..1, (p - q) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact fren_small p q hp hq ht.1 ht.2 (le_trans ht.2 hle)
      have e2 : ∫ t in (1 : ℝ)..a, fren p q t = ∫ t in (1 : ℝ)..a, (p * t⁻¹ - q) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hle] at ht
        exact fren_mid2 p q hp hq (lt_of_lt_of_le zero_lt_one ht.1) ht.1 ht.2
      have h1 : IntervalIntegrable (fun t : ℝ => p * t⁻¹) volume 1 a := by
        refine (ContinuousOn.mul continuousOn_const
          (ContinuousOn.inv₀ continuousOn_id ?_)).intervalIntegrable
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
      rw [e1, e2, intervalIntegral.integral_sub h1 intervalIntegral.intervalIntegrable_const,
        intervalIntegral.integral_const, intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one ha0]
      simp only [smul_eq_mul, sub_zero, div_one]
      nlinarith [haq]

/-- The sum over `i` of the scalar Frenkel integrands. -/
lemma sum_fren {n : Type*} [Fintype n] (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (t : ℝ) :
    ∑ i, fren (p i) (q i) t
      = ((∑ i, max (p i - t * q i) 0) - (∑ i, p i) * max (1 - t) 0) / t := by
  have h : ∀ i, fren (p i) (q i) t = (max (p i - t * q i) 0 - p i * max (1 - t) 0) / t :=
    fun i => fren_eq_posPart _ _ _ (hp i)
  simp only [h, sub_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul]

/-- The Frenkel integrand of a pair of probability vectors is nonnegative. -/
lemma sum_fren_nonneg {n : Type*} [Fintype n] (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑ i, fren (p i) (q i) t := by
  rw [sum_fren p q hp t, hp1, one_mul]
  apply div_nonneg _ ht.le
  rw [sub_nonneg]
  rcases le_total (1 - t) 0 with h | h
  · rw [max_eq_right h]
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
  · rw [max_eq_left h]
    calc 1 - t = ∑ i, (p i - t * q i) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, hq1]; ring
      _ ≤ ∑ i, max (p i - t * q i) 0 := Finset.sum_le_sum fun i _ => le_max_left _ _

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma diagonal_sub_smul (p q : n → ℝ) (t : ℝ) :
    (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        - (t : ℂ) • (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
      = Matrix.diagonal (fun i => ((p i - t * q i : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j <;> simp [h]

lemma re_trace_diagonal (p : n → ℝ) :
    ((Matrix.diagonal fun i => ((p i : ℝ) : ℂ)).trace).re = ∑ i, p i := by
  simp [Matrix.trace_diagonal, Complex.re_sum]

/-- **The commuting case**: for two (strictly positive) probability vectors, the integral formula
defining `QI.relEntropy` returns the classical Kullback-Leibler divergence
`∑ᵢ pᵢ log (pᵢ / qᵢ)`. -/
theorem relEntropy_diagonal (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    relEntropy (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
      = ENNReal.ofReal (∑ i, p i * Real.log (p i / q i)) := by
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      (posPartTrace ((Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
            - (t : ℂ) • (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)))
          - ENNReal.ofReal ((Matrix.diagonal fun i => ((p i : ℝ) : ℂ)).trace.re
              * max 0 (1 - t))) / ENNReal.ofReal t
        = ENNReal.ofReal (∑ i, fren (p i) (q i) t) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [diagonal_sub_smul, posPartTrace_diagonal, re_trace_diagonal, hp1, one_mul,
      max_comm (0 : ℝ) (1 - t), ← ENNReal.ofReal_sub _ (le_max_right _ _),
      ← ENNReal.ofReal_div_of_pos ht0]
    congr 1
    rw [sum_fren p q hp t, hp1, one_mul]
  have hint : ∀ i : n, IntegrableOn (fren (p i) (q i)) (Ioi 0) :=
    fun i => integrableOn_fren (p i) (q i) (hp i) (hq i)
  have hintsum : IntegrableOn (fun t => ∑ i, fren (p i) (q i) t) (Ioi 0) :=
    integrable_finset_sum _ fun i _ => hint i
  rw [relEntropy, setLIntegral_congr_fun measurableSet_Ioi hcongr,
    ← ofReal_integral_eq_lintegral_ofReal hintsum
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
        fun t ht => sum_fren_nonneg p q hp hp1 hq1 ht))]
  congr 1
  rw [integral_finset_sum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => integral_fren (p i) (q i) (hp i) (hq i)

end QI

