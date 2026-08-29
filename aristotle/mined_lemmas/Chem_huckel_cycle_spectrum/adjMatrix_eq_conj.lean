import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

namespace Chem

open Matrix Complex

/-! ## The `n`-th root of unity and its basic arithmetic -/

section Roots

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma adjMatrix_eq_conj (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = (fourierUnit n : Matrix (Fin n) (Fin n) ℂ) * huckelDiag n
        * ((fourierUnit n)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  have hFG : fourierMat n * fourierMatInv n = 1 := fourierMat_mul_inv n
  calc ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = ((SimpleGraph.cycleGraph n).adjMatrix ℂ) * (fourierMat n * fourierMatInv n) := by
        rw [hFG, mul_one]
    _ = (((SimpleGraph.cycleGraph n).adjMatrix ℂ) * fourierMat n) * fourierMatInv n :=
        (mul_assoc _ _ _).symm
    _ = (fourierMat n * huckelDiag n) * fourierMatInv n := by rw [adj_mul_fourier n hn]

end Diagonalize

/-- **Hückel spectrum of the cycle graph.**  For `n ≥ 3`, the eigenvalues (spectrum) of the
adjacency matrix of the cycle graph `C n` are exactly the numbers `2 cos (2 π k / n)`
for `k = 0, …, n - 1`.  These are the Hückel π-electron energy levels (in units of the
resonance integral `β`, measured relative to the Coulomb integral `α`). -/
