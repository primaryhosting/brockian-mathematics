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

/-
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1` for every
prime `p` dividing `n`. -/

theorem isCarmichael_iff_fermat {n : ℕ} :
    IsCarmichael n ↔ 1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n] := by
  constructor
  · rintro hC
    exact ⟨hC.1, hC.2.1, fun a => isCarmichael_fermat hC a⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, squarefree_of_fermat h1 h3, fun p hp => korselt_of_fermat h1 h3 hp⟩

section Chernick

variable {k : ℕ}

/-- Chernick's identity: `(6k+1)(12k+1)(18k+1) = 36k(36k² + 11k + 1) + 1`. -/
