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

import Mathlib
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem coprime_moduli_aux {W k k' : ℕ} (hk : k ≤ W) (h : k' < k) :
    Nat.Coprime (1 + (k + 1) * (W !)) (1 + (k' + 1) * (W !)) := by
  by_contra hg
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hA : p ∣ 1 + (k + 1) * (W !) := hpg.trans (Nat.gcd_dvd_left _ _)
  have hB : p ∣ 1 + (k' + 1) * (W !) := hpg.trans (Nat.gcd_dvd_right _ _)
  have hfac : ¬ (p ∣ W !) := by
    intro hd
    have h2 : p ∣ (k' + 1) * (W !) := Dvd.dvd.mul_left hd _
    have : p ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [Nat.add_comm] at hB)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hdiff : p ∣ (k - k') * (W !) := by
    have hd := Nat.dvd_sub hA hB
    have e : 1 + (k + 1) * (W !) - (1 + (k' + 1) * (W !)) = (k - k') * (W !) := by
      have : (k + 1) * (W !) - (k' + 1) * (W !) = (k - k') * W ! := by
        rw [← Nat.sub_mul]; congr 1; omega
      omega
    rwa [e] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hdiff with h1 | h1
  · exact hfac (Nat.dvd_factorial hp.pos (le_trans (Nat.le_of_dvd (by omega) h1) (by omega)))
  · exact hfac h1

