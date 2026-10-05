/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/

theorem hodgeConjecture_of_Hpp_eq_bot (X : HodgeDatum)
    (h : X.Hpq ((X.p : ℤ), (X.p : ℤ)) = ⊥) : HodgeConjecture X := by
  intro v hv
  have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ X.Hpq ((X.p : ℤ), (X.p : ℤ)) := hv
  rw [h, Submodule.mem_bot] at hv'
  have hv0 : v = 0 := incl_injective X.V (by simpa using hv')
  rw [hv0]
  exact X.alg.zero_mem

/-- **Base case: `H^{2p}` of rank at most one.** If the cohomology group is at most
one-dimensional (e.g. `H^0` of a connected variety, or `H^{2n}` of an `n`-dimensional one)
and carries at least one nonzero algebraic class (e.g. the fundamental class, or the class
of a point), then the Hodge conjecture holds for `X`. -/
