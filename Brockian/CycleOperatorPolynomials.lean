import Mathlib
import Brockian.CyclicFourierStructure
import Brockian.CyclePolynomialCertificates

/-!
# Cycle-operator annihilators from the shared Fourier lemma

This uses Fourier completeness to pass from the scalar eigenvalue identities
to operator identities. The coordinate matrix is explicitly the adjacency
operator f(j) ↦ f(j+1)+f(j−1).
-/

namespace Brockian.CycleOperatorPolynomials

open Brockian.CyclicFourierStructure Brockian.CyclePolynomialCertificates
open Polynomial

variable (N : ℕ) [NeZero N]

def adjacency : Module.End ℂ (ZMod N → ℂ) where
  toFun f j := f (j + 1) + f (j - 1)
  map_add' f g := by ext j; simp; ring
  map_smul' c f := by ext j; simp [mul_add]

theorem adjacency_mode (k : ZMod N) :
    adjacency N (mode k) =
      (ZMod.stdAddChar k + ZMod.stdAddChar (-k)) • mode k := by
  simpa [adjacency, huckel, shift, shiftInv] using huckel_mode 0 1 k

theorem annihilator_of_eigenvalues (p : ℂ[X])
    (hp : ∀ k : ZMod N, p.eval (ZMod.stdAddChar k + ZMod.stdAddChar (-k)) = 0) :
    aeval (adjacency N) p = 0 := by
  classical
  apply LinearMap.ext
  intro f
  change (aeval (adjacency N) p) f = 0
  rw [← projector_resolution f, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  simp only [projector, map_smul]
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (adjacency_mode N k), hp k]
  simp

def fivePolynomial : ℂ[X] := (X - C 2) * (X ^ 2 + X - C 1)
def thirteenPolynomial : ℂ[X] :=
  (X - C 2) * (X ^ 6 + X ^ 5 - C 5 * X ^ 4 - C 4 * X ^ 3 +
    C 6 * X ^ 2 + C 3 * X - C 1)

theorem five_annihilator : aeval (adjacency 5) fivePolynomial = 0 := by
  apply annihilator_of_eigenvalues
  intro k
  simpa [fivePolynomial] using five_fourier_eigenvalue k

theorem thirteen_annihilator : aeval (adjacency 13) thirteenPolynomial = 0 := by
  apply annihilator_of_eigenvalues
  intro k
  simpa [thirteenPolynomial, psi13] using thirteen_fourier_eigenvalue k

theorem five_operator_identity :
    (adjacency 5 - 2) * (adjacency 5 ^ 2 + adjacency 5 - 1) = 0 := by
  simpa [fivePolynomial] using five_annihilator

theorem thirteen_operator_identity :
    (adjacency 13 - 2) * (adjacency 13 ^ 6 + adjacency 13 ^ 5 -
      5 * adjacency 13 ^ 4 - 4 * adjacency 13 ^ 3 + 6 * adjacency 13 ^ 2 +
      3 * adjacency 13 - 1) = 0 := by
  simpa [thirteenPolynomial] using thirteen_annihilator

noncomputable def adjacencyMatrix : Matrix (ZMod N) (ZMod N) ℂ :=
  LinearMap.toMatrixAlgEquiv' (adjacency N)

theorem adjacencyMatrix_apply (i j : ZMod N) :
    adjacencyMatrix N i j = (if i + 1 = j then 1 else 0) +
      (if i - 1 = j then 1 else 0) := by
  classical
  simp [adjacencyMatrix, LinearMap.toMatrixAlgEquiv'_apply, adjacency, Pi.single_apply,
    eq_comm]

theorem five_matrix_identity :
    (adjacencyMatrix 5 - 2) * (adjacencyMatrix 5 ^ 2 + adjacencyMatrix 5 - 1) = 0 := by
  have h := congrArg (LinearMap.toMatrixAlgEquiv' :
    Module.End ℂ (ZMod 5 → ℂ) → Matrix (ZMod 5) (ZMod 5) ℂ) five_operator_identity
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat, map_one, map_zero,
    adjacencyMatrix] using h

theorem thirteen_matrix_identity :
    (adjacencyMatrix 13 - 2) * (adjacencyMatrix 13 ^ 6 + adjacencyMatrix 13 ^ 5 -
      5 * adjacencyMatrix 13 ^ 4 - 4 * adjacencyMatrix 13 ^ 3 +
      6 * adjacencyMatrix 13 ^ 2 + 3 * adjacencyMatrix 13 - 1) = 0 := by
  have h := congrArg (LinearMap.toMatrixAlgEquiv' :
    Module.End ℂ (ZMod 13 → ℂ) → Matrix (ZMod 13) (ZMod 13) ℂ) thirteen_operator_identity
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat, map_one, map_zero,
    adjacencyMatrix] using h

end Brockian.CycleOperatorPolynomials
