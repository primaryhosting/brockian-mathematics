import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

theorem purification_exists.{u} {n : Type u} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (∃ ψ : n × n → ℂ, IsPurification ρ ψ ∧ ∑ p, ‖ψ p‖ ^ 2 = 1) ∧
      (∀ (m : Type u) [Fintype m] [DecidableEq m] (ψ φ : n × m → ℂ),
        IsPurification ρ ψ → IsPurification ρ φ →
        ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
          ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * U k j) ∧
      (∀ (m m' : Type u) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
        (ψ : n × m → ℂ) (φ : n × m' → ℂ), IsPurification ρ ψ → IsPurification ρ φ →
        Fintype.card m ≤ Fintype.card m' →
        ∃ V : Matrix m m' ℂ, V * Vᴴ = 1 ∧ ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * V k j) :=
  ⟨exists_purification hρ htr,
    fun _ _ _ ψ φ hψ hφ => purification_unique_up_to_unitary ψ φ hψ hφ,
    fun _ _ _ _ _ _ ψ φ hψ hφ hcard =>
      purification_unique_up_to_isometry ψ φ hψ hφ hcard⟩

end QI

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

