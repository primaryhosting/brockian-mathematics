import Mathlib
import RequestProject.Classical

/-!
# Quantum relative entropy

Definitions of the matrix logarithm (via the continuous functional calculus), the Umegaki
relative entropy of two density matrices, and quantum channels in Kraus form.
-/

open Matrix Unitary
open scoped BigOperators ComplexOrder

namespace QI

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The matrix logarithm of a Hermitian matrix, defined through the continuous functional
calculus (with the convention `log 0 = 0`, so that vanishing eigenvalues contribute nothing). -/
noncomputable def matLog (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- The Umegaki relative entropy `D(ρ‖σ) = Tr ρ (log ρ - log σ)` of two density matrices. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * (matLog ρ - matLog σ))).re

/-- A density matrix: a positive semidefinite matrix of unit trace. -/
structure IsState (ρ : Matrix n n ℂ) : Prop where
  posSemidef : ρ.PosSemidef
  trace_one : ρ.trace = 1

/-- Two matrices are *simultaneously diagonalizable* when a single unitary diagonalizes both
of them (equivalently, for Hermitian matrices, when they commute). -/
def SimulDiag (A B : Matrix n n ℂ) : Prop :=
  ∃ (U : unitary (Matrix n n ℂ)) (a b : n → ℝ),
    A = (U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ) ∧
    B = (U : Matrix n n ℂ) * diagonal (fun i => (b i : ℂ)) * star (U : Matrix n n ℂ)

/-- A quantum channel in Kraus form: `X ↦ ∑ i, K i * X * (K i)ᴴ`. Together with the
condition `∑ i, (K i)ᴴ * K i = 1` this is precisely a CPTP map. -/
noncomputable def krausMap (K : ι → Matrix n m ℂ) (X : Matrix m m ℂ) : Matrix n n ℂ :=
  ∑ i, K i * X * (K i)ᴴ

/-! ### Functional calculus lemmas -/

theorem isSelfAdjoint_diagonal (d : n → ℝ) :
    IsSelfAdjoint (diagonal fun i => (d i : ℂ)) := by
  show (diagonal fun i => (d i : ℂ)).IsHermitian
  rw [Matrix.IsHermitian]
  simp [Matrix.diagonal_conjTranspose]

theorem spectrum_real_diagonal (d : n → ℝ) :
    spectrum ℝ (diagonal fun i => (d i : ℂ)) ⊆ Set.range d := by
  intro r hr
  by_contra hrange
  rw [spectrum.mem_iff] at hr
  apply hr
  have hdiag : algebraMap ℝ (Matrix n n ℂ) r - (diagonal fun i => (d i : ℂ))
      = diagonal (fun i => ((r : ℂ) - (d i : ℂ))) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [hdiag, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  rw [isUnit_iff_ne_zero]
  simp only [sub_ne_zero]
  intro h
  exact hrange ⟨i, by exact_mod_cast h.symm⟩

theorem aeval_diagonal (d : n → ℝ) (P : Polynomial ℝ) :
    (Polynomial.aeval (diagonal fun i => (d i : ℂ))) P
      = diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  have h1 : (diagonal fun i => (d i : ℂ)) = Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) := rfl
  rw [h1, Polynomial.aeval_algHom_apply]
  have h3 : (Polynomial.aeval (fun i => (d i : ℂ))) P = fun i => ((P.eval (d i) : ℝ) : ℂ) := by
    funext i
    have hpi := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : n => ℂ) i)
      (fun j => (d j : ℂ)) P
    simp only [Pi.evalAlgHom_apply] at hpi
    rw [← hpi]
    have h2 := Polynomial.aeval_algHom_apply (Algebra.ofId ℝ ℂ) (d i) P
    simp only [Algebra.ofId_apply] at h2
    simpa using h2
  rw [h3]
  rfl

/-- The continuous functional calculus of a real diagonal matrix acts entrywise. -/
theorem cfc_diagonal (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal fun i => (d i : ℂ)) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  have hA : IsSelfAdjoint (diagonal fun i => (d i : ℂ)) := isSelfAdjoint_diagonal d
  set s : Finset ℝ := Finset.image d Finset.univ with hs
  set P : Polynomial ℝ := Lagrange.interpolate s id f with hP
  have hnode : ∀ i : n, P.eval (d i) = f (d i) := by
    intro i
    have hmem : d i ∈ s := by simp [hs]
    have := Lagrange.eval_interpolate_at_node (F := ℝ) (ι := ℝ) (s := s) (v := id) f
      (Set.injOn_id _) hmem
    simpa [hP] using this
  have h1 : cfc f (diagonal fun i => (d i : ℂ))
      = cfc (fun x => P.eval x) (diagonal fun i => (d i : ℂ)) := by
    refine cfc_congr ?_
    intro r hr
    obtain ⟨i, rfl⟩ := spectrum_real_diagonal d hr
    exact (hnode i).symm
  rw [h1, cfc_polynomial P _ hA, aeval_diagonal d P]
  simp only [hnode]

/-- The continuous functional calculus commutes with conjugation by a unitary. -/
theorem cfc_unitary_conj (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) (A : Matrix n n ℂ)
    (hA : IsSelfAdjoint A) :
    cfc f ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * cfc f A * star (U : Matrix n n ℂ) := by
  have hfun : ((conjStarAlgAut ℝ (Matrix n n ℂ) U) : Matrix n n ℂ → Matrix n n ℂ)
      = fun x => (U : Matrix n n ℂ) * x * star (U : Matrix n n ℂ) := rfl
  have hcont : Continuous ((conjStarAlgAut ℝ (Matrix n n ℂ) U) : Matrix n n ℂ → Matrix n n ℂ) := by
    rw [hfun]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) (conjStarAlgAut ℝ (Matrix n n ℂ) U) f A
    (by rw [continuousOn_iff_continuous_restrict]; fun_prop) hcont hA
  simpa using this.symm

/-- `matLog` of a diagonalized matrix. -/
theorem matLog_conj_diagonal (U : unitary (Matrix n n ℂ)) (d : n → ℝ) :
    matLog ((U : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ) := by
  rw [matLog, cfc_unitary_conj U Real.log _ (isSelfAdjoint_diagonal d), cfc_diagonal]

/-! ### Relative entropy of a simultaneously diagonalized pair -/

theorem relEntropy_conj_diagonal (U : unitary (Matrix n n ℂ)) (p q : n → ℝ) :
    relEntropy ((U : Matrix n n ℂ) * diagonal (fun i => (p i : ℂ)) * star (U : Matrix n n ℂ))
        ((U : Matrix n n ℂ) * diagonal (fun i => (q i : ℂ)) * star (U : Matrix n n ℂ))
      = klDiv p q := by
  have hU1 : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.2.1
  rw [relEntropy, matLog_conj_diagonal, matLog_conj_diagonal]
  have hprod : ((U : Matrix n n ℂ) * diagonal (fun i => (p i : ℂ)) * star (U : Matrix n n ℂ)) *
      ((U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ)
        - (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * (diagonal (fun i => (p i : ℂ)) *
          (diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
            - diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ)))) * star (U : Matrix n n ℂ) := by
    have : ∀ X Y : Matrix n n ℂ,
        ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) *
          ((U : Matrix n n ℂ) * Y * star (U : Matrix n n ℂ))
          = (U : Matrix n n ℂ) * (X * Y) * star (U : Matrix n n ℂ) := by
      intro X Y
      calc ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) *
          ((U : Matrix n n ℂ) * Y * star (U : Matrix n n ℂ))
          = (U : Matrix n n ℂ) * X * (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ))
            * Y * star (U : Matrix n n ℂ) := by noncomm_ring
        _ = (U : Matrix n n ℂ) * (X * Y) * star (U : Matrix n n ℂ) := by
            rw [hU1]; noncomm_ring
    have hsub : (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ)
        - (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ)
        = (U : Matrix n n ℂ) * (diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
            - diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ))) * star (U : Matrix n n ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [hsub, this]
  rw [hprod]
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hdd : (diagonal fun i => (p i : ℂ)) *
      ((diagonal fun i => ((Real.log (p i) : ℝ) : ℂ))
        - diagonal fun i => ((Real.log (q i) : ℝ) : ℂ))
      = diagonal (fun i => (p i : ℂ) *
          (((Real.log (p i) : ℝ) : ℂ) - ((Real.log (q i) : ℝ) : ℂ))) := by
    rw [Matrix.mul_sub, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, mul_sub]
  rw [hdd, Matrix.trace_diagonal, klDiv]
  push_cast
  simp [Complex.re_sum]

end QI

import Mathlib

/-!
# Classical relative entropy and the classical data-processing inequality

This file develops the classical (commutative) part of the data-processing inequality:
the Kullback–Leibler divergence of two probability vectors does not increase when both
are pushed through a stochastic map.
-/

open scoped BigOperators

namespace QI

variable {ι κ : Type*}

/-- Kullback–Leibler divergence of two nonnegative vectors, with the usual conventions
`0 * log 0 = 0` (implemented through `Real.log 0 = 0`). -/
noncomputable def klDiv [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * (Real.log (p i) - Real.log (q i))

/-- The log-sum inequality. -/
theorem log_sum_le [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * (Real.log (∑ i, a i) - Real.log (∑ i, b i))
      ≤ ∑ i, a i * (Real.log (a i) - Real.log (b i)) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hs : ∑ i, a i = 0 := by rw [← hA]; exact hA0'.symm
    have hzero : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hs i (Finset.mem_univ i)
    simp [hzero, ← hA0']
  · have hBpos : 0 < B := by
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ B from Finset.sum_nonneg fun i _ => hb i) with h | h
      · exfalso
        have hs : ∑ i, b i = 0 := by rw [← hB]; exact h.symm
        have hb0 : ∀ i, b i = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 hs i (Finset.mem_univ i)
        have hz : ∀ i, a i = 0 := fun i => hab i (hb0 i)
        rw [hA] at hApos
        simp [hz] at hApos
      · exact h
    have key : ∀ i, a i * (Real.log A - Real.log B) + (a i - b i * (A / B))
        ≤ a i * (Real.log (a i) - Real.log (b i)) := by
      intro i
      rcases eq_or_lt_of_le (ha i) with hai | hai
      · have hbi : 0 ≤ b i * (A / B) := mul_nonneg (hb i) (by positivity)
        rw [← hai]
        simp
        linarith
      · have hbi : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with h | h
          · exact absurd (hab i h.symm) (by linarith)
          · exact h
        have ht : 0 < b i * A / (a i * B) := by positivity
        have hlog := Real.log_le_sub_one_of_pos ht
        have hlogeq : Real.log (b i * A / (a i * B))
            = Real.log (b i) + Real.log A - Real.log (a i) - Real.log B := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
            (by positivity), Real.log_mul (by positivity) (by positivity)]
          ring
        rw [hlogeq] at hlog
        have hkey : a i * (Real.log (a i) - Real.log (b i) - (Real.log A - Real.log B))
            ≥ a i * (1 - b i * A / (a i * B)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hai)
          linarith
        have h2 : a i * (1 - b i * A / (a i * B)) = a i - b i * (A / B) := by
          field_simp
        rw [h2] at hkey
        nlinarith [hkey]
    have hsum : ∑ i, (a i * (Real.log A - Real.log B) + (a i - b i * (A / B)))
        = A * (Real.log A - Real.log B) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hA, ← hB]
      field_simp
      ring
    calc A * (Real.log A - Real.log B)
        = ∑ i, (a i * (Real.log A - Real.log B) + (a i - b i * (A / B))) := hsum.symm
      _ ≤ ∑ i, a i * (Real.log (a i) - Real.log (b i)) := Finset.sum_le_sum fun i _ => key i

/-- **Classical data-processing inequality**: the Kullback–Leibler divergence is monotone
under (column-)stochastic maps. -/
theorem klDiv_stochastic_le [Fintype ι] [Fintype κ] (S : κ → ι → ℝ)
    (hS : ∀ k i, 0 ≤ S k i) (hcol : ∀ i, ∑ k, S k i = 1)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    klDiv (fun k => ∑ i, S k i * p i) (fun k => ∑ i, S k i * q i) ≤ klDiv p q := by
  have step : ∀ k : κ,
      (∑ i, S k i * p i) * (Real.log (∑ i, S k i * p i) - Real.log (∑ i, S k i * q i))
        ≤ ∑ i, S k i * (p i * (Real.log (p i) - Real.log (q i))) := by
    intro k
    have h := log_sum_le (fun i => S k i * p i) (fun i => S k i * q i)
      (fun i => mul_nonneg (hS k i) (hp i)) (fun i => mul_nonneg (hS k i) (le_of_lt (hq i)))
      (fun i hi => by
        rcases mul_eq_zero.1 hi with h0 | h0
        · simp [h0]
        · exact absurd h0 (ne_of_gt (hq i)))
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_lt_of_le (hS k i) with h0 | h0
    · simp [← h0]
    · rcases eq_or_lt_of_le (hp i) with hp0 | hp0
      · simp [← hp0]
      · rw [Real.log_mul (ne_of_gt h0) (ne_of_gt hp0),
          Real.log_mul (ne_of_gt h0) (ne_of_gt (hq i))]
        ring
  calc klDiv (fun k => ∑ i, S k i * p i) (fun k => ∑ i, S k i * q i)
      ≤ ∑ k, ∑ i, S k i * (p i * (Real.log (p i) - Real.log (q i))) :=
        Finset.sum_le_sum fun k _ => step k
    _ = klDiv p q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hcol i, one_mul]

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

