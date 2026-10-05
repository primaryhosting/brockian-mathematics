/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A proof of Cauchy's theorem: if a prime `p` divides the order of a finite group `G`,
then `G` has an element of order `p`.

The argument here is the classical one, by strong induction on `|G|`:

* if some proper subgroup `H < G` has order divisible by `p`, apply the induction hypothesis
  to `H`;
* otherwise the class equation forces `p ∣ |Z(G)|`, so `Z(G)` is not proper, i.e. `G` is
  abelian.  Picking `x ≠ 1` and setting `H = ⟨x⟩`, either `H = G` (and then `p ∣ orderOf x`),
  or `H` is proper and `p ∣ [G : H] = |G ⧸ H| < |G|`, so the induction hypothesis produces an
  element of order `p` in the quotient, which lifts to an element of `G` whose order is
  divisible by `p`.
-/

namespace Math

namespace CauchyProof

/-- From an element whose order is divisible by the prime `p` one extracts an element of
order exactly `p`. -/
theorem exists_orderOf_eq_of_dvd_orderOf {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (g : G)
    (hg : 0 < orderOf g) (hdvd : p ∣ orderOf g) : ∃ h : G, orderOf h = p := by
  refine ⟨g ^ (orderOf g / p), ?_⟩
  have hne : orderOf g / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hg hdvd) hp.pos).ne'
  rw [orderOf_pow' g hne, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
    Nat.div_div_self hdvd hg.ne']

/-- The size of the conjugacy class of `g` times the size of the centralizer of `g`
is the order of the group. -/
theorem card_carrier_mul_card_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card ((ConjClasses.mk g).carrier) * Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card G := by
  classical
  cases nonempty_fintype G
  have hstab : Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card (MulAction.stabilizer (ConjAct G) g) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (Equiv.refl _) fun y => ?_
    simp [MulAction.mem_stabilizer_iff, ConjAct.smul_def, Subgroup.mem_centralizer_iff,
      ConjAct.ofConjAct, eq_comm, eq_mul_inv_iff_mul_eq]
    exact Iff.rfl
  have horb : Nat.card ((ConjClasses.mk g).carrier) =
      Nat.card (MulAction.orbit (ConjAct G) g) := by
    rw [ConjAct.orbit_eq_carrier_conjClasses]
  rw [hstab, horb]
  simpa [Nat.card_eq_fintype_card, ConjAct.card] using
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g

/-- An element whose conjugacy class has more than one element is not central. -/
theorem notMem_center_of_mem_noncenter {G : Type*} [Group G] {g : G}
    (hg : ConjClasses.mk g ∈ ConjClasses.noncenter G) : g ∉ Subgroup.center G := by
  intro hc
  rw [ConjClasses.mem_noncenter] at hg
  refine hg.not_subsingleton ?_
  intro a ha b hb
  rw [ConjClasses.carrier_eq_preimage_mk] at ha hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj] at ha hb
  have hcs : g ∈ Set.center G := Set.mem_center_iff.mpr hc
  have haux : ∀ c : G, IsConj c g → c = g := fun _ hcg => hcg.eq_of_right_mem_center hcs
  rw [haux a ha, haux b hb]

/-- Key consequence of the class equation: if no proper subgroup of the finite group `G` has
order divisible by the prime `p`, but `p ∣ |G|`, then `p` divides the order of the centre. -/
theorem prime_dvd_card_center {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G)
    (hprop : ∀ H : Subgroup G, H ≠ ⊤ → ¬ p ∣ Nat.card H) :
    p ∣ Nat.card (Subgroup.center G) := by
  classical
  have key := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  have hfin : (ConjClasses.noncenter G).Finite := Set.toFinite _
  have hterm : ∀ x ∈ ConjClasses.noncenter G, p ∣ Nat.card x.carrier := by
    intro x hx
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
    have hgc : g ∉ Subgroup.center G := notMem_center_of_mem_noncenter hx
    have hcent : Subgroup.centralizer ({g} : Set G) ≠ ⊤ := by
      intro h
      exact hgc (Subgroup.centralizer_eq_top_iff_subset.mp h (Set.mem_singleton g))
    have hnd : ¬ p ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) := hprop _ hcent
    have hmul := card_carrier_mul_card_centralizer (G := G) g
    rw [← hmul] at hdvd
    exact (hp.dvd_mul.mp hdvd).resolve_right hnd
  have hsum : p ∣ ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := by
    have hEq : ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier
        = ∑ x ∈ hfin.toFinset, Nat.card x.carrier := by
      rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
    rw [hEq]
    exact Finset.dvd_sum fun i hi => hterm i (hfin.mem_toFinset.mp hi)
  have : p ∣ Nat.card (Subgroup.center G) +
      ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := key ▸ hdvd
  exact (Nat.dvd_add_iff_left hsum).mpr this

/-- The main induction: Cauchy's theorem for groups of order `n`. -/
theorem exists_orderOf_eq_prime_aux {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → p ∣ n → ∃ g : G, orderOf g = p := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ hcard hdvd
    subst hcard
    by_cases hsub : ∃ H : Subgroup G, H ≠ ⊤ ∧ p ∣ Nat.card H
    · -- a proper subgroup already has order divisible by `p`
      obtain ⟨H, hne, hd⟩ := hsub
      have hpos : 0 < Nat.card H := Nat.card_pos
      have hdvdG : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
      have hlt : Nat.card H < Nat.card G := by
        refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvdG) ?_
        intro hEq
        exact hne (Subgroup.eq_top_of_card_eq H hEq)
      obtain ⟨x, hx⟩ := IH (Nat.card H) hlt H rfl hd
      exact ⟨(x : G), by rw [Subgroup.orderOf_coe, hx]⟩
    · push_neg at hsub
      -- the class equation makes `G` abelian
      have hcenter := prime_dvd_card_center hp hdvd hsub
      have htop : Subgroup.center G = ⊤ := by
        by_contra hne
        exact hsub _ hne hcenter
      have hcomm : ∀ a b : G, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
      -- pick a nontrivial element
      have hcard1 : Nat.card G ≠ 1 := by
        intro h
        rw [h] at hdvd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
      have hnontriv : Nontrivial G := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        exact lt_of_le_of_ne Nat.card_pos (Ne.symm hcard1)
      obtain ⟨x, hx⟩ := exists_ne (1 : G)
      set H := Subgroup.zpowers x with hH
      have hordx : 1 < orderOf x := by
        have h0 : 0 < orderOf x := orderOf_pos x
        have h1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
        omega
      have hcardH : Nat.card H = orderOf x := Nat.card_zpowers x
      by_cases htopH : H = ⊤
      · -- `G` is cyclic, generated by `x`
        have : Nat.card G = orderOf x := by
          rw [← hcardH, htopH, Subgroup.card_top]
        exact exists_orderOf_eq_of_dvd_orderOf hp x (by omega) (this ▸ hdvd)
      · -- pass to the quotient by `⟨x⟩`
        have hnp : ¬ p ∣ Nat.card H := hsub H htopH
        haveI : H.Normal := ⟨by
          intro a ha b
          have : b * a * b⁻¹ = a := by
            rw [hcomm b a]
            group
          rw [this]; exact ha⟩
        have hindex : H.index * Nat.card H = Nat.card G := Subgroup.index_mul_card H
        have hpi : p ∣ H.index := by
          have : p ∣ H.index * Nat.card H := hindex ▸ hdvd
          exact (hp.dvd_mul.mp this).resolve_right hnp
        have hqcard : Nat.card (G ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
        have hlt : Nat.card (G ⧸ H) < Nat.card G := by
          rw [hqcard, ← hindex]
          have hipos : 0 < H.index := Nat.pos_of_ne_zero (by
            intro h
            rw [h, zero_mul] at hindex
            exact absurd hindex.symm Nat.card_pos.ne')
          have : 2 ≤ Nat.card H := by omega
          nlinarith
        obtain ⟨q, hq⟩ := IH (Nat.card (G ⧸ H)) hlt (G ⧸ H) rfl (hqcard ▸ hpi)
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        have hdy : p ∣ orderOf y := by
          have := orderOf_map_dvd (QuotientGroup.mk' H) y
          rw [QuotientGroup.mk'_apply, hq] at this
          exact this
        exact exists_orderOf_eq_of_dvd_orderOf hp y (orderOf_pos y) hdy

end CauchyProof

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order exactly `p`. -/
theorem cauchy_group {G : Type*} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  CauchyProof.exists_orderOf_eq_prime_aux hp (Nat.card G) G rfl
    (by simpa [Nat.card_eq_fintype_card] using hdvd)

/-- Cauchy's theorem, stated with `Nat.card` for a `Finite` group. -/
theorem cauchy_group_natCard {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ g : G, orderOf g = p :=
  CauchyProof.exists_orderOf_eq_prime_aux hp (Nat.card G) G rfl hdvd

/-- Cauchy's theorem, subgroup form: if a prime `p` divides `|G|` then `G` has a subgroup
of order `p`. -/
theorem cauchy_group_subgroup {G : Type*} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) : ∃ H : Subgroup G, Nat.card H = p := by
  obtain ⟨g, hg⟩ := cauchy_group hp hdvd
  exact ⟨Subgroup.zpowers g, by rw [Nat.card_zpowers, hg]⟩

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

