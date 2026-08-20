import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma schrodinger_symm_basis (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) (m n : ℤ) :
    ⟪schrodingerBasisImage b V m, b n⟫_ℂ = ⟪b m, schrodingerBasisImage b V n⟫_ℂ := by
  simp only [schrodingerBasisImage, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_basis, map_add, map_ofNat, Complex.conj_ofReal]
  by_cases h1 : m = n
  · subst h1
    simp [show (m : ℤ) ≠ m - 1 by omega, show (m : ℤ) ≠ m + 1 by omega,
      show ¬ (m + 1 = m) by omega, show ¬ (m - 1 = m) by omega]
  · have h4 : (m + 1 = n) ↔ (m = n - 1) := by omega
    have h5 : (m - 1 = n) ↔ (m = n + 1) := by omega
    simp only [h1, h4, h5, if_false]
    by_cases h6 : m = n - 1 <;> by_cases h7 : m = n + 1 <;> simp_all

/-- The Schrödinger operator is symmetric on its domain. -/
