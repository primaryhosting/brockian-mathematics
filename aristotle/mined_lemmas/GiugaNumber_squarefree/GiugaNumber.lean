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


lemma GiugaNumber.squarefree {n : ℕ} (h : GiugaNumber n) : Squarefree n := by
  obtain ⟨hn1, -, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hcon
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hcon
  have h1 : p ∣ n / p - 1 := hdvd p hp hpn
  obtain ⟨k, hk⟩ := hcon
  have h2 : p ∣ n / p := ⟨k, by rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have hone : p ∣ 1 := by
    have := Nat.dvd_sub h2 h1
    rwa [Nat.sub_sub_self hpos] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

