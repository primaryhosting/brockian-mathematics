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

theorem supported_ad {S : Set (Fin N)} {A : SpinOp N} (s : Finset ι) (h : ι → SpinOp N)
    (X : ι → Set (Fin N)) (hloc : ∀ i ∈ s, Supported (X i) (h i))
    (hdiam : ∀ i ∈ s, ∀ a ∈ X i, ∀ b ∈ X i, |(a : ℤ) - (b : ℤ)| ≤ 1)
    (hA : Supported S A) : Supported (nbhd S) (ad (∑ i ∈ s, h i) A) := by
  have hexp : ad (∑ i ∈ s, h i) A = ∑ i ∈ s, (h i * A - A * h i) := by
    rw [ad, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hexp]
  refine supported_sum s _ (fun i hi => ?_)
  by_cases hdis : Disjoint (X i) S
  · have hcomm := commute_of_disjoint hdis (hloc i hi) hA
    rw [hcomm, sub_self]
    exact supported_zero _
  · rw [Set.not_disjoint_iff] at hdis
    obtain ⟨z, hzX, hzS⟩ := hdis
    have hsub : X i ∪ S ⊆ nbhd S := by
      rintro j (hj | hj)
      · exact ⟨z, hzS, hdiam i hi j hj z hzX⟩
      · exact subset_nbhd S hj
    have hsub' : S ∪ X i ⊆ nbhd S := by rw [Set.union_comm]; exact hsub
    exact supported_sub (supported_mono hsub (supported_mul (hloc i hi) hA))
      (supported_mono hsub' (supported_mul hA (hloc i hi)))

/-- After `m` steps of the Heisenberg generator the support has grown by at most `m` sites. -/
