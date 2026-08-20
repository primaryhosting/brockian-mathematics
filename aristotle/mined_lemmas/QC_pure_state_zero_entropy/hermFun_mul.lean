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

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Functional calculus for a Hermitian matrix: `hermFun hρ f` is the matrix obtained by
applying the real function `f` to the eigenvalues of `ρ`, in an eigenbasis of `ρ`. -/

lemma hermFun_mul {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (f g : ℝ → ℝ) :
    hermFun hρ f * hermFun hρ g = hermFun hρ (fun x => f x * g x) := by
  have hU : star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      (hρ.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
  simp only [hermFun]
  calc (hρ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ))
        * star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        ((hρ.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (fun i => ((g (hρ.eigenvalues i) : ℝ) : ℂ)) *
          star (hρ.eigenvectorUnitary : Matrix n n ℂ))
      = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)) *
        (star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
          (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
        (diagonal (fun i => ((g (hρ.eigenvalues i) : ℝ) : ℂ)) *
          star (hρ.eigenvectorUnitary : Matrix n n ℂ)) := by
        simp only [mul_assoc]
    _ = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        (diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)) *
          diagonal (fun i => ((g (hρ.eigenvalues i) : ℝ) : ℂ))) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
        rw [hU, mul_one]; simp only [mul_assoc]
    _ = _ := by rw [Matrix.diagonal_mul_diagonal]; push_cast; ring_nf

/-- `mulLog hρ` really is the product of `ρ` with the matrix logarithm of `ρ`. -/
