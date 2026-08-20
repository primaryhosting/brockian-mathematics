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
