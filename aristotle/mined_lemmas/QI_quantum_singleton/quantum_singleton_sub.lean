/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

theorem quantum_singleton_sub {q n k d K : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hd1 : 1 ≤ d)
    (hK : K = q ^ k) (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (hV : Vᴴ * V = 1)
    (hdist : ∀ S : Finset (Fin n), S.card < d → Correctable V S) :
    2 * (d - 1) ≤ n - k := by
  have h := quantum_singleton hq hk hd1 hK V hV hdist
  omega

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

