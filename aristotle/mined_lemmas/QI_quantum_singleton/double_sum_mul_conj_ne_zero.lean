/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix Module ComplexConjugate
open scoped ComplexOrder

/-! ## Part I : linear algebra over `ℂ`

The mathematical core of the quantum Singleton bound is a statement about the ranks of the
various flattenings of a four-index complex tensor.  This part develops the required
rank inequalities.
-/

/-- Every column of a complex matrix can be expanded in a family of `X.rank` vectors, with
coefficients that are (fixed) linear functionals applied to the column. -/

theorem double_sum_mul_conj_ne_zero {B C : Type*} [Fintype B] [Fintype C] (f : B → C → ℂ)
    (b0 : B) (c0 : C) (h : f b0 c0 ≠ 0) : (∑ b, ∑ c, f b c * conj (f b c)) ≠ 0 := by
  have hcast : (∑ b, ∑ c, f b c * conj (f b c))
      = ((∑ b, ∑ c, Complex.normSq (f b c) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
      simp [Complex.mul_conj]
  rw [hcast]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hz
  have hnn : ∀ b ∈ Finset.univ, (0:ℝ) ≤ ∑ c, Complex.normSq (f b c) :=
    fun b _ => Finset.sum_nonneg fun c _ => Complex.normSq_nonneg _
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz b0 (Finset.mem_univ _)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c (_ : c ∈ Finset.univ) => Complex.normSq_nonneg (f b0 c))).mp h5 c0 (Finset.mem_univ _)
  exact h (by simpa [Complex.normSq_eq_zero] using h6)

/-- **Core of the quantum Singleton bound.**

Let `T i a b c` be the coefficients of `card R` orthonormal vectors (indexed by `i : R`) in a
tripartite system `A ⊗ B ⊗ C`.  Assume that the reduced correlations on `A` and on `B` are
codeword independent (`hA`, `hB`), i.e. erasures of `A` and of `B` are correctable.  Then
`card R ≤ card C`. -/
