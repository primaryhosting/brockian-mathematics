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

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem infinite_dvd_woodall {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    {n : ℕ | p ∣ woodall n}.Infinite := by
  obtain ⟨n₀, hn₀, hdvd₀⟩ := exists_dvd_woodall hp hodd
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  set T := p * (p - 1) with hT
  have hTpos : 0 < T := Nat.mul_pos (by omega) (by omega)
  have key : ∀ j : ℕ, 1 ≤ n₀ + j * T ∧ p ∣ woodall (n₀ + j * T) := by
    intro j
    induction j with
    | zero => simpa using ⟨hn₀, hdvd₀⟩
    | succ k ih =>
      obtain ⟨hk1, hk2⟩ := ih
      refine ⟨by nlinarith [hk1], ?_⟩
      have := (dvd_woodall_periodic hp hodd hk1).mp hk2
      have heq : n₀ + k * T + T = n₀ + (k + 1) * T := by ring
      rwa [heq] at this
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => n₀ + j * T)
  case hi =>
    intro a b hab
    simp only at hab
    have : a * T = b * T := by omega
    exact Nat.eq_of_mul_eq_mul_right hTpos this
  case hf =>
    intro j
    exact (key j).2

end Brockian.CullenWoodall

