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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem prime_pow_of_introspective
    (n r p B : ℕ) (hp : p.Prime)
    (hn : 2 ≤ n) (hB : n < 2 ^ B) (hr2 : 2 ≤ r) (hcopn : Nat.Coprime n r)
    (hpn : p ∣ n) (hrp : r < p)
    (hord : ∀ i, 1 ≤ i → i ≤ 100 * B ^ 2 → (n : ZMod r) ^ i ≠ 1)
    (hintro : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * B →
        Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X])) :
    ∃ k, n = p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero r := ⟨by omega⟩
  have hcopp : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpn hcopn
  obtain ⟨d0, hd0⟩ : ∃ d0 : ℕ, d0 = orderOf (ZMod.unitOfCoprime p hcopp) := ⟨_, rfl⟩
  have hd0pos : 0 < d0 := hd0 ▸ orderOf_pos _
  let K := GaloisField p d0
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ d0 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p d0 hd0pos.ne'
  have hcardU : Fintype.card Kˣ = p ^ d0 - 1 := by
    rw [Fintype.card_units, hcardK]
  have hppos : 0 < p ^ d0 := Nat.pow_pos hp.pos
  have hrdvd : r ∣ Fintype.card Kˣ := by
    rw [hcardU]
    have h1 : ((p ^ d0 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      have h3 : (((ZMod.unitOfCoprime p hcopp) ^ d0 : (ZMod r)ˣ) : ZMod r) = 1 := by
        rw [hd0, pow_orderOf_eq_one]; simp
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at h3
      push_cast
      simpa using h3
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
    exact (Nat.modEq_iff_dvd' (by omega)).1 h4.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hNcard : Nat.card Kˣ = Fintype.card Kˣ := Nat.card_eq_fintype_card
  have hp2 : 1 < p ^ d0 := Nat.one_lt_pow hd0pos.ne' hp.one_lt
  have hNpos : 0 < Nat.card Kˣ := by rw [hNcard, hcardU]; omega
  have hrN : r ∣ Nat.card Kˣ := by rw [hNcard]; exact hrdvd
  have hdiv0 : Nat.card Kˣ / r ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd hNpos hrN) (by omega : 0 < r)
    omega
  have hxord : orderOf ((g ^ (Nat.card Kˣ / r) : Kˣ) : K) = r := by
    rw [orderOf_units, orderOf_pow' g hdiv0, hg,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hrN)]
    exact Nat.div_div_self hrN (by omega)
  exact prime_pow_of_introspective_aux n r p B (K := K) ((g ^ (Nat.card Kˣ / r) : Kˣ) : K) hxord
    hn hB hr2 hcopn hpn hrp hord hintro

end AKS

import Mathlib
import RequestProject.AKS.Core

/-!
# Existence of a small auxiliary modulus `r`

The AKS algorithm needs a modulus `r` for which the multiplicative order of `n` modulo `r`
exceeds a given threshold `K`.  This file shows that such an `r` can always be found below
`2 * B * K ^ 2`, where `n < 2 ^ B`.  The proof uses the classical fact that
`lcm (1, …, 2M)` is at least `binomial(2M, M) ≥ 2 ^ M`.
-/

namespace AKS

/-- `lcmUpTo m = lcm (1, 2, …, m)`. -/
