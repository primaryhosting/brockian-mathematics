/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open MulAction Subgroup

/-- From an element whose order is divisible by `p` we get an element of order exactly `p`. -/

theorem prime_dvd_card_center {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G)
    (hproper : ∀ H : Subgroup G, H ≠ ⊤ → ¬ p ∣ Nat.card H) :
    p ∣ Nat.card (Subgroup.center G) := by
  classical
  cases nonempty_fintype G
  have key : ∀ x ∈ ConjClasses.noncenter G, p ∣ Nat.card x.carrier := by
    rintro x hx
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
    have hcard := card_carrier_mul_card_centralizer g
    have hne : Subgroup.centralizer ({g} : Set G) ≠ ⊤ := by
      intro htop
      rw [htop] at hcard
      have h1 : Nat.card (ConjClasses.mk g).carrier = 1 := by
        have hpos : 0 < Nat.card G := Nat.card_pos
        rw [Subgroup.card_top] at hcard
        have : Nat.card (ConjClasses.mk g).carrier * Nat.card G = 1 * Nat.card G := by
          simpa using hcard
        exact Nat.eq_of_mul_eq_mul_right hpos this
      rw [ConjClasses.mem_noncenter] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      have : Subsingleton (ConjClasses.mk g).carrier := Nat.card_eq_one_iff_unique.mp h1 |>.1
      exact hab (congrArg Subtype.val (this.elim ⟨a, ha⟩ ⟨b, hb⟩))
    have hnd := hproper _ hne
    have : p ∣ Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({g} : Set G)) := hcard ▸ hdvd
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h
    · exact absurd h hnd
  have hclass := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  have hsum : p ∣ ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := by
    have hfin : (ConjClasses.noncenter G).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.dvd_sum ?_
    intro i hi
    exact key i (hfin.mem_toFinset.mp hi)
  have h : p ∣ Nat.card (Subgroup.center G) +
      ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := hclass ▸ hdvd
  exact (Nat.dvd_add_iff_left hsum).mpr h

/-- Auxiliary form of Cauchy's theorem, proved by strong induction on the order of the group. -/
