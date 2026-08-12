/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import RequestProject.CauchySelfContained

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order `p`.

The proof is self-contained (it does not invoke Mathlib's `exists_prime_orderOf_dvd_card`):
see `Math.cauchy_of_dvd_card`, which argues by strong induction on the order of the group. -/
theorem cauchy_group {G : Type*} [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
  have hcard : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
  exact cauchy_of_dvd_card p hp (Nat.card G) (hcard ▸ hdvd) G inferInstance inferInstance rfl

end Math

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
# Cauchy's theorem, proved by induction on the order of the group

This file gives a proof of Cauchy's theorem that does not use Mathlib's
`exists_prime_orderOf_dvd_card`.  The argument is the classical one, by strong
induction on `Nat.card G`:

* if some proper subgroup has order divisible by `p`, apply the inductive hypothesis to it;
* otherwise the class equation forces the centre to be all of `G`, so `G` is abelian, and
  the abelian case is handled by passing to the quotient by a cyclic subgroup.
-/

universe u

namespace Math

/-- The statement of Cauchy's theorem for groups of a fixed order `n`. -/
def CauchyAt (p n : ℕ) : Prop :=
  ∀ (G : Type u) (_ : Group G) (_ : Finite G), Nat.card G = n → ∃ g : G, orderOf g = p

/-- If the order of `x` is divisible by `p`, then some power of `x` has order exactly `p`. -/
lemma exists_orderOf_eq_of_dvd_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ} {x : G}
    (h : p ∣ orderOf x) : ∃ g : G, orderOf g = p :=
  ⟨x ^ (orderOf x / p), orderOf_pow_orderOf_div (orderOf_pos x).ne' h⟩

/-- A proper subgroup of a finite group is strictly smaller than the group. -/
lemma card_subgroup_lt_card_of_ne_top {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : H ≠ ⊤) : Nat.card H < Nat.card G := by
  have hd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hne : Nat.card H ≠ Nat.card G := fun he => h (Subgroup.eq_top_of_card_eq H he)
  exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hd) hne

/-- Orbit-stabilizer for the conjugation action: the size of the conjugacy class of `g` times
the order of its centralizer is the order of the group. -/
lemma card_conjClass_mul_card_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  classical
  cases nonempty_fintype G
  have h1 : (ConjClasses.mk g).carrier = MulAction.orbit (ConjAct G) g :=
    (ConjAct.orbit_eq_carrier_conjClasses g).symm
  have h2 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have h3 : MulAction.stabilizer (ConjAct G) g = Subgroup.centralizer {ConjAct.toConjAct g} :=
    ConjAct.stabilizer_eq_centralizer g
  have h5 : Nat.card ↑(MulAction.stabilizer (ConjAct G) g)
      = Nat.card ↑(Subgroup.centralizer ({g} : Set G)) := by
    rw [h3]
    rfl
  have h4 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.ofConjAct.toEquiv
  calc Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g})
      = Nat.card (MulAction.orbit (ConjAct G) g)
          * Nat.card ↑(MulAction.stabilizer (ConjAct G) g) := by rw [h1, h5]
    _ = Nat.card (ConjAct G) := by simpa [Nat.card_eq_fintype_card] using h2
    _ = Nat.card G := h4

/-- If no proper subgroup of `G` has order divisible by the prime `p`, but `p` divides the
order of `G`, then `G` is its own centre. -/
lemma center_eq_top_of_no_proper_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card G)
    (hmin : ∀ H : Subgroup G, H ≠ ⊤ → ¬ p ∣ Nat.card H) :
    Subgroup.center G = ⊤ := by
  classical
  by_contra hne
  refine hmin _ hne ?_
  have hclass := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  have hfin : (ConjClasses.noncenter G).Finite := Set.toFinite _
  have hsum : p ∣ ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.dvd_sum ?_
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
    have hgc : g ∉ Subgroup.center G := fun hg => (ConjClasses.mk_bijOn G).mapsTo hg hx
    have hnetop : Subgroup.centralizer ({g} : Set G) ≠ ⊤ := fun h =>
      hgc (Subgroup.centralizer_eq_top_iff_subset.mp h rfl)
    have h2 : p ∣ Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) := by
      rw [card_conjClass_mul_card_centralizer g]; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · exact h
    · exact absurd h (hmin _ hnetop)
  have heq : Nat.card (Subgroup.center G)
      = Nat.card G - ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := by omega
  rw [heq]
  exact Nat.dvd_sub hdvd hsum

/-- The abelian case of Cauchy's theorem, assuming the result for all smaller groups. -/
lemma cauchy_abelian {G : Type u} [CommGroup G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) (IH : ∀ m < Nat.card G, p ∣ m → CauchyAt.{u} p m) :
    ∃ g : G, orderOf g = p := by
  have h1 : 1 < Nat.card G := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hdvd)
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  set H := Subgroup.zpowers x with hH
  have hcardH : Nat.card H = orderOf x := Nat.card_zpowers x
  have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have h1' : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hHone : 1 < Nat.card H := by rw [hcardH]; omega
  by_cases hdx : p ∣ orderOf x
  · exact exists_orderOf_eq_of_dvd_orderOf hdx
  · have hmul : Nat.card G = Nat.card (G ⧸ H) * Nat.card H :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H
    have hdq : p ∣ Nat.card (G ⧸ H) := by
      have hpm : p ∣ Nat.card (G ⧸ H) * Nat.card H := hmul ▸ hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hpm with h | h
      · exact h
      · exact absurd (hcardH ▸ h) hdx
    have hqlt : Nat.card (G ⧸ H) < Nat.card G := by
      have := Nat.card_pos (α := G ⧸ H)
      nlinarith [hmul]
    obtain ⟨y', hy'⟩ := IH _ hqlt hdq (G ⧸ H) inferInstance inferInstance rfl
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
    refine exists_orderOf_eq_of_dvd_orderOf (x := y) ?_
    rw [← hy']
    exact orderOf_map_dvd (QuotientGroup.mk' H) y

/-- Cauchy's theorem, by strong induction on the order of the group. -/
theorem cauchy_of_dvd_card (p : ℕ) (hp : p.Prime) :
    ∀ n : ℕ, p ∣ n → CauchyAt.{u} p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hdvd G _ _ hcard
    subst hcard
    by_cases hsub : ∃ H : Subgroup G, H ≠ ⊤ ∧ p ∣ Nat.card H
    · obtain ⟨H, hHne, hHdvd⟩ := hsub
      have hlt : Nat.card H < Nat.card G :=
        card_subgroup_lt_card_of_ne_top hHne
      obtain ⟨g, hg⟩ := IH (Nat.card H) hlt hHdvd H inferInstance inferInstance rfl
      exact ⟨(g : G), by simpa using hg⟩
    · push_neg at hsub
      have hcenter : Subgroup.center G = ⊤ :=
        center_eq_top_of_no_proper_subgroup hp hdvd (fun H hH => hsub H hH)
      let _ : CommGroup G := Group.commGroupOfCenterEqTop hcenter
      exact cauchy_abelian hp hdvd (fun m hm hm' => IH m hm hm')

end Math

