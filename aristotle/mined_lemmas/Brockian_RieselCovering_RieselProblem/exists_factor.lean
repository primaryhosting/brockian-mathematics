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

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RieselCovering

/-- `IsComposite N` means that `N` factors as a product of two factors, each `> 1`. -/

theorem exists_factor (n : Nat) :
    ∃ m : Nat, 509203 * 2 ^ n = 1 + cov (n % 24) * m := by
  obtain ⟨h1, h2, hP, hK⟩ := cov_spec (n % 24) (Nat.mod_lt _ (by omega))
  obtain ⟨s, hs⟩ := pow24_mul (cov (n % 24)) (cofP (n % 24)) hP (n / 24)
  refine ⟨cofK (n % 24) + s + cov (n % 24) * cofK (n % 24) * s, ?_⟩
  have hn : n = 24 * (n / 24) + n % 24 := (Nat.div_add_mod n 24).symm
  have hpow : (2 : Nat) ^ n = 2 ^ (24 * (n / 24)) * 2 ^ (n % 24) := by
    rw [← Nat.pow_add, ← hn]
  rw [hpow]
  have e1 : 509203 * (2 ^ (24 * (n / 24)) * 2 ^ (n % 24))
      = (509203 * 2 ^ (n % 24)) * 2 ^ (24 * (n / 24)) := by
    rw [Nat.mul_comm (2 ^ (24 * (n / 24))) (2 ^ (n % 24)), ← Nat.mul_assoc]
  rw [e1, hK, hs]
  grind

/-- **Riesel's theorem** (1956): `509203` is a Riesel number, i.e. `509203 * 2 ^ n - 1`
is composite for every `n ≥ 1`.  The proof is the classical covering-congruence argument
using the covering set `{3, 5, 7, 13, 17, 241}` of divisors of `2 ^ 24 - 1`,
whose multiplicative orders `2, 4, 3, 12, 8, 24` for the base `2` cover all residues
modulo `24`. -/
