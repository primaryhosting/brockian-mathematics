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

theorem lieb_robinson_XX {N : ℕ} (x y : Fin N) (K : ℕ)
    (hK : (K : ℤ) < |(x : ℤ) - (y : ℤ)|) (t : ℂ) :
    Commute (∑ m ∈ Finset.range (K + 1), (t ^ m / (m ! : ℂ)) •
      adPow (∑ p ∈ nnPairs N, pauliX p.1 * pauliX p.2) m (pauliX x)) (pauliX y) := by
  refine lieb_robinson (nnPairs N) _ (fun p => {p.1, p.2}) (fun p _ => ?_)
    (fun p hp a ha b hb => ?_) _ _ x y (supported_pauliX x) (supported_pauliX y) K hK t
  · have hmul := supported_mul (supported_pauliX p.1) (supported_pauliX p.2)
    rwa [Set.singleton_union] at hmul
  · have hp12 : |(p.1 : ℤ) - (p.2 : ℤ)| ≤ 1 := (Finset.mem_filter.mp hp).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first
      | exact hp12
      | (rw [abs_sub_comm]; exact hp12)
      | simp

end Frontier

