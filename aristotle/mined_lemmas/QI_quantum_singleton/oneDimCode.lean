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

def oneDimCode (q n d : ℕ) (s0 : Str n q) : QECC q n 0 d where
  space := Submodule.span ℂ {(EuclideanSpace.single s0 (1 : ℂ) : HSpace n q)}
  dim := by
    have hne : (EuclideanSpace.single s0 (1 : ℂ) : HSpace n q) ≠ 0 := by
      intro h
      have := congrFun (congrArg WithLp.ofLp h) s0
      simp at this
    rw [finrank_span_singleton hne, pow_zero]
  detects S _ := by
    refine ⟨fun u v => corr S (EuclideanSpace.single s0 (1 : ℂ)) (EuclideanSpace.single s0 1) u v,
      ?_⟩
    intro x hx y hy u v
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hcorr : ∀ z z' : HSpace n q, corr S (a • z) (b • z') u v
        = conj a * b * corr S z z' u v := by
      intro z z'
      simp only [corr, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hone : inner ℂ (EuclideanSpace.single s0 (1 : ℂ) : HSpace n q)
        (EuclideanSpace.single s0 (1 : ℂ)) = 1 := by simp
    rw [hcorr, inner_smul_left, inner_smul_right, hone]
    ring


end QI

#print axioms QI.quantum_singleton

