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

theorem korselt_of_fermat {n : ℕ} (hn : 1 < n) (h : ∀ a : ℕ, a ^ n ≡ a [MOD n])
    {p : ℕ} (hp : p ∈ n.primeFactors) : (p - 1) ∣ (n - 1) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set a : ℕ := ((g : ZMod p)).val with ha
  have hcast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha, ZMod.natCast_val, ZMod.cast_id]
  have hmod : a ^ n ≡ a [MOD p] := Nat.ModEq.of_dvd hpn (h a)
  have hz : ((a : ZMod p)) ^ n = (a : ZMod p) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at this
    exact this
  rw [hcast] at hz
  have hgn : g ^ n = g := by
    ext
    push_cast
    exact hz
  have hone : g ^ (n - 1) = 1 := by
    have h2 : g ^ (n - 1) * g = 1 * g := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
      exact hgn
    exact mul_right_cancel h2
  have hdvd := orderOf_dvd_of_pow_eq_one hone
  rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hpp] at hdvd

/-- **Korselt's criterion**: a composite `n` is a Fermat pseudoprime to every base if and
only if it is squarefree and `p - 1 ∣ n - 1` for every prime factor `p`.  This shows that
`IsCarmichael` agrees with the classical definition of a Carmichael number. -/
