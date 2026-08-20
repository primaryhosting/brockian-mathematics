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

theorem lieb_robinson {N : ℕ} {ι : Type*} (s : Finset ι) (h : ι → SpinOp N)
    (X : ι → Set (Fin N)) (hloc : ∀ i ∈ s, Supported (X i) (h i))
    (hdiam : ∀ i ∈ s, ∀ a ∈ X i, ∀ b ∈ X i, |(a : ℤ) - (b : ℤ)| ≤ 1)
    (A B : SpinOp N) (x y : Fin N) (hA : Supported {x} A) (hB : Supported {y} B)
    (K : ℕ) (hK : (K : ℤ) < |(x : ℤ) - (y : ℤ)|) (t : ℂ) :
    Commute (∑ m ∈ Finset.range (K + 1), (t ^ m / (m ! : ℂ)) • adPow (∑ i ∈ s, h i) m A) B := by
  have hball : ∀ m ∈ Finset.range (K + 1),
      Supported {j : Fin N | |(j : ℤ) - (x : ℤ)| ≤ (K : ℤ)}
        ((t ^ m / (m ! : ℂ)) • adPow (∑ i ∈ s, h i) m A) := by
    intro m hm
    have hmK : (m : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    refine supported_smul _ (supported_mono ?_ (supported_adPow s h X hloc hdiam hA m))
    intro j hj
    have hjm := nbhdIter_singleton_subset x m hj
    simp only [Set.mem_setOf_eq] at hjm ⊢
    linarith
  have hsum := supported_sum (Finset.range (K + 1)) _ hball
  have hdisj : Disjoint {j : Fin N | |(j : ℤ) - (x : ℤ)| ≤ (K : ℤ)} ({y} : Set (Fin N)) := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_setOf_eq]
    intro hy
    rw [abs_sub_comm] at hK
    linarith
  exact commute_of_disjoint hdisj hsum hB

/-!
## Non-vacuity

The hypotheses of `lieb_robinson` are satisfied by a genuine nearest-neighbour spin chain:
the Pauli `X` operators are nonzero observables supported on a single site, and the
`XX`-chain Hamiltonian `∑ ⟨p,q⟩ nearest neighbours, X_p X_q` is a sum of terms supported on
sets of sites of diameter at most one.
-/

/-- The Pauli `X` operator at site `k` (spin flip at `k`, identity elsewhere). -/
