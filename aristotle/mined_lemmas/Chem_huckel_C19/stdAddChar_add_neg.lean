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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-!
# Hückel spectrum of the cycle `C₁₉`

We compute the spectrum of the adjacency matrix of Mathlib's cycle graph on `19` vertices
(the Hückel matrix of the annulene `C₁₉H₁₉`, with `α = 0`, `β = 1`), showing it is exactly
the set of numbers `2 * cos (2 π k / 19)` for `k = 0, …, 18`.

The vertex type `Fin 19` of `SimpleGraph.cycleGraph 19` is definitionally `ZMod 19`, and we
freely work with the ring structure of `ZMod 19` on it.  The eigenvectors are the additive
characters `j ↦ e (j * k)`, assembled into the discrete Fourier matrix `Chem.dftMatrix`.
-/

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of `C₁₉H₁₉`
(with Coulomb integral `α = 0` and resonance integral `β = 1`). -/

lemma stdAddChar_add_neg (k : ZMod 19) :
    ZMod.stdAddChar k + ZMod.stdAddChar (-k)
      = ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ) := by
  have h1 : ZMod.stdAddChar (-k) = Complex.exp (-(2 * Real.pi * Complex.I * k.val / 19)) := by
    have h2 : ZMod.stdAddChar (-k) * ZMod.stdAddChar k = 1 := by
      rw [← ZMod.stdAddChar.map_add_eq_mul]; simp
    rw [stdAddChar_eq_exp k] at h2
    rw [Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_left h2
  rw [stdAddChar_eq_exp k, h1,
    show ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)
        = 2 * Complex.cos ((2 * Real.pi * k.val / 19 : ℝ) : ℂ) by
      push_cast [Complex.ofReal_cos]; ring,
    Complex.cos]
  push_cast
  ring_nf

/-- Orthogonality of the characters of `ZMod 19`. -/
