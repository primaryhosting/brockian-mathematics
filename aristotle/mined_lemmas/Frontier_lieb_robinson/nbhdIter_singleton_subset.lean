/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean 4 requires `import` commands to
-- precede every other command, including module doc-strings.)

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

namespace Frontier

/-- Spin configurations of a chain of `N` sites (each site carries a qubit). -/
abbrev Config (N : ℕ) := Fin N → Fin 2

/-- Observables of the spin chain: linear operators on the `2^N`-dimensional Hilbert space,
represented as matrices indexed by spin configurations. -/
abbrev SpinOp (N : ℕ) := Matrix (Config N) (Config N) ℂ

/-- `Supported S M` says that the observable `M` acts only on the sites in `S`, i.e.
`M = M₀ ⊗ 1` with `M₀` acting on the sites of `S`.  Concretely, matrix elements vanish
unless the configurations agree off `S`, and they depend only on the restrictions to `S`. -/

theorem nbhdIter_singleton_subset {N : ℕ} (x : Fin N) (m : ℕ) :
    nbhdIter m ({x} : Set (Fin N)) ⊆ {j | |(j : ℤ) - (x : ℤ)| ≤ m} := by
  induction m with
  | zero =>
    intro j hj
    simp only [nbhdIter, Set.mem_singleton_iff] at hj
    subst hj
    simp
  | succ m ih =>
    intro j hj
    simp only [nbhdIter, nbhd, Set.mem_setOf_eq] at hj
    obtain ⟨z, hz, hjz⟩ := hj
    have h1 : |(z : ℤ) - (x : ℤ)| ≤ (m : ℤ) := ih hz
    have h2 : |(j : ℤ) - (x : ℤ)| ≤ |(j : ℤ) - (z : ℤ)| + |(z : ℤ) - (x : ℤ)| := abs_sub_le _ _ _
    simp only [Set.mem_setOf_eq]
    push_cast
    linarith

end

/-- **Lieb–Robinson bound (strict light cone for a nearest-neighbour spin chain).**

Let `H = ∑ i ∈ s, h i` be a Hamiltonian on a chain of `N` qubits which is a sum of
interaction terms `h i`, each supported on a set `X i` of sites of diameter at most `1`
(nearest-neighbour interactions).  Let `A` be an observable at site `x` and `B` an
observable at site `y`.  Then every Taylor truncation, to order `K < |x - y|`, of the
Heisenberg evolution `τ_t(A) = ∑ₘ (tᵐ/m!) adᴴ ᵐ (A)` of `A` commutes *exactly* with `B`.

This is the base case of the Lieb–Robinson bound: information cannot leave the light cone
`|x - y| ≤ (order in t)`; all contributions to `[τ_t(A), B]` come from orders at least
`|x - y|`, whose size is controlled by `(2‖H‖|t|)^{|x-y|}/|x-y|!`. -/
