/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

noncomputable def rho {m n : ℕ} (ψ : Fin m → Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i i' => ∑ j, ψ i j * (starRingEnd ℂ) (ψ i' j)

/-- `IsSchmidt ψ σ u v` says that `ψ i j = ∑ k, σ k * u k i * v k j` is a Schmidt
decomposition of the bipartite vector `ψ`: the Schmidt coefficients `σ k` are positive reals
and the families `u`, `v` are orthonormal. -/
structure IsSchmidt {m n r : ℕ} (ψ : Fin m → Fin n → ℂ) (σ : Fin r → ℝ)
    (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ) : Prop where
  pos : ∀ k, 0 < σ k
  onu : IsON u
  onv : IsON v
  decomp : ∀ i j, ψ i j = ∑ k, (σ k : ℂ) * u k i * v k j

/-- Swapping a double sum and pulling out the factor not depending on the outer index. -/
