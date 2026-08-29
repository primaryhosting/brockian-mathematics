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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ZumkellerNumbers

open Finset

/-- A natural number `n` is a *Zumkeller number* if it is positive and its set of divisors
can be split into two parts of equal sum; equivalently, some set `S` of divisors of `n`
satisfies `2 * ∑ S = σ₁ n`. -/

lemma injOn_mul_divisors {m n : ℕ} (hcop : m.Coprime n) (S : Finset ℕ) (hS : S ⊆ m.divisors) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ((S ×ˢ n.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [Finset.mem_coe, Finset.mem_product] at hab hcd
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨hc, hd⟩ := hcd
  have ham : a ∣ m := (Nat.mem_divisors.1 (hS ha)).1
  have hcm : c ∣ m := (Nat.mem_divisors.1 (hS hc)).1
  have hbn : b ∣ n := (Nat.mem_divisors.1 hb).1
  have hdn : d ∣ n := (Nat.mem_divisors.1 hd).1
  have hapos : 0 < a := Nat.pos_of_mem_divisors (hS ha)
  have had : a.Coprime d :=
    Nat.Coprime.coprime_dvd_left ham (Nat.Coprime.coprime_dvd_right hdn hcop)
  have hcb : c.Coprime b :=
    Nat.Coprime.coprime_dvd_left hcm (Nat.Coprime.coprime_dvd_right hbn hcop)
  simp only at h
  have h1 : a ∣ c := had.dvd_of_dvd_mul_right (h ▸ Dvd.intro b rfl)
  have h2 : c ∣ a := hcb.dvd_of_dvd_mul_right (h ▸ Dvd.intro d rfl)
  have hac : a = c := Nat.dvd_antisymm h1 h2
  subst hac
  have hbd : b = d := Nat.eq_of_mul_eq_mul_left hapos h
  simp [hbd]

/-- If `m` is Zumkeller and `n` is a positive number coprime to `m`, then `m * n` is Zumkeller. -/
