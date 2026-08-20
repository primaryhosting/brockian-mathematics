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

theorem squarefree_of_fermat {n : ℕ} (hn : 1 < n) (h : ∀ a : ℕ, a ^ n ≡ a [MOD n]) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hdvd
  have hx2 : 2 ≤ x := hx.two_le
  have hle : x ≤ x ^ n := Nat.le_self_pow (by omega) x
  have hn' : n ∣ x ^ n - x := (Nat.modEq_iff_dvd' hle).mp (h x).symm
  have hxx : x * x ∣ x ^ n - x := dvd_trans hdvd hn'
  have hxxn : x * x ∣ x ^ n := by
    refine ⟨x ^ (n - 2), ?_⟩
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  have hdvdx : x * x ∣ x := by
    have := Nat.dvd_sub hxxn hxx
    simpa [Nat.sub_sub_self hle] using this
  have := Nat.le_of_dvd (by omega) hdvdx
  nlinarith

/-- If `n > 1` is a Fermat pseudoprime to every base, then `p - 1 ∣ n - 1` for every prime
factor `p` of `n`.  The proof uses a primitive root modulo `p`. -/
