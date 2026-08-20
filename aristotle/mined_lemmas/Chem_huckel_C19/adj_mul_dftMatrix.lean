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

lemma adj_mul_dftMatrix : C19adjMatrix * dftMatrix = dftMatrix * eigDiag := by
  ext i k
  rw [Matrix.mul_apply, eigDiag, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 19) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 19) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 19, j ≠ i - 1 → j ≠ i + 1 → C19adjMatrix i j * dftMatrix j k = 0 := by
    intro j h1 h2
    rw [C19adjMatrix_apply, if_neg, zero_mul]
    rintro (h | h)
    · exact h1 (by linear_combination -h)
    · exact h2 (by linear_combination h)
  rw [Finset.sum_eq_add_of_mem (i - 1) (i + 1) (Finset.mem_univ _) (Finset.mem_univ _) hne
    (by intro j _ hj; exact key j hj.1 hj.2)]
  simp only [C19adjMatrix_apply, dftMatrix, Matrix.of_apply]
  rw [if_pos (by left; ring), if_pos (by right; ring),
    show (i - 1) * k = i * k + -k by ring, show (i + 1) * k = i * k + k by ring,
    ZMod.stdAddChar.map_add_eq_mul, ZMod.stdAddChar.map_add_eq_mul]
  ring

/-- The spectrum of a diagonal matrix is the range of its diagonal. -/
