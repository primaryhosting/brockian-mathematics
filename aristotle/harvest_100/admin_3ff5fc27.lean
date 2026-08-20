import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-!
## McKay's proof of Cauchy's theorem

The whole argument is developed from scratch here: we consider the set of lists of length `p`
of elements of `G` whose product is `1`, let the cyclic group `ZMod p` act on it by rotation,
and compare the cardinality of this set (which is `|G| ^ (p-1)`, divisible by `p`) with the
cardinality of the set of fixed points (constant lists `[g, …, g]` with `g ^ p = 1`) modulo `p`.
-/

/-- The set of lists of length `p` of elements of `G` whose product is `1`. -/
def ProdOne (G : Type*) [Group G] (p : ℕ) : Type _ :=
  {l : List G // l.length = p ∧ l.prod = 1}

namespace ProdOne

variable {G : Type*} [Group G] {p : ℕ}

@[ext]
theorem ext {x y : ProdOne G p} (h : x.1 = y.1) : x = y := Subtype.ext h

instance [Finite G] : Finite (ProdOne G p) := by
  cases nonempty_fintype G
  haveI : Finite (List.Vector G p) := inferInstance
  refine Finite.of_injective (β := List.Vector G p)
    (fun x : ProdOne G p => (⟨x.1, x.2.1⟩ : List.Vector G p)) ?_
  intro x y hxy
  exact ext (congrArg (fun v : List.Vector G p => v.1) hxy)

/-- Rotation gives an action of the cyclic group `Multiplicative (ZMod p)` on `ProdOne G p`. -/
instance instMulAction [NeZero p] :
    MulAction (Multiplicative (ZMod p)) (ProdOne G p) where
  smul k x :=
    ⟨x.1.rotate (Multiplicative.toAdd k).val,
      ⟨by rw [List.length_rotate, x.2.1], List.prod_rotate_eq_one_of_prod_eq_one x.2.2 _⟩⟩
  one_smul x := by
    apply ext
    show x.1.rotate (ZMod.val (0 : ZMod p)) = x.1
    simp
  mul_smul k l x := by
    apply ext
    have hlen : x.1.length = p := x.2.1
    have hmod : ∀ m : ℕ, x.1.rotate (m % p) = x.1.rotate m := by
      intro m
      have h := List.rotate_mod x.1 m
      rwa [hlen] at h
    show x.1.rotate ((Multiplicative.toAdd k + Multiplicative.toAdd l)).val
      = (x.1.rotate (Multiplicative.toAdd l).val).rotate (Multiplicative.toAdd k).val
    rw [List.rotate_rotate, ZMod.val_add, hmod, Nat.add_comm]

theorem smul_val [NeZero p] (k : Multiplicative (ZMod p)) (x : ProdOne G p) :
    (k • x).1 = x.1.rotate (Multiplicative.toAdd k).val := rfl

/-- The trivial element `[1, 1, …, 1]`. -/
def trivialVec (G : Type*) [Group G] (p : ℕ) : ProdOne G p :=
  ⟨List.replicate p 1, by simp, by simp⟩

theorem trivialVec_mem_fixedPoints [NeZero p] :
    trivialVec G p ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) (ProdOne G p) := by
  intro k
  apply ext
  rw [smul_val]
  exact List.rotate_replicate 1 p _

/-- Deleting the last entry identifies `ProdOne G p` with the lists of length `p - 1`
(the last entry is forced to be the inverse of the product of the others). -/
def equivVector (hp : 0 < p) : ProdOne G p ≃ List.Vector G (p - 1) where
  toFun x := ⟨x.1.dropLast, by
    rw [List.length_dropLast, x.2.1]⟩
  invFun w := ⟨w.1 ++ [w.1.prod⁻¹], by
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, w.2, List.length_singleton]
      omega
    · simp⟩
  left_inv x := by
    apply ext
    have hne : x.1 ≠ [] := by
      intro h
      have hl := x.2.1
      rw [h, List.length_nil] at hl
      omega
    show x.1.dropLast ++ [x.1.dropLast.prod⁻¹] = x.1
    obtain ⟨d, a, hd⟩ : ∃ d a, x.1 = d ++ [a] :=
      ⟨x.1.dropLast, x.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hprod : d.prod * a = 1 := by
      have h2 := x.2.2
      rw [hd, List.prod_append] at h2
      simpa using h2
    rw [hd, List.dropLast_concat, eq_inv_of_mul_eq_one_left hprod, inv_inv]
  right_inv w := by
    apply Subtype.ext
    show (w.1 ++ [w.1.prod⁻¹]).dropLast = w.1
    exact List.dropLast_concat

theorem card_eq [Fintype G] (hp : 0 < p) :
    Nat.card (ProdOne G p) = Fintype.card G ^ (p - 1) := by
  rw [Nat.card_congr (equivVector hp), Nat.card_eq_fintype_card, card_vector]

/-- A fixed point of the rotation action is a constant list. -/
theorem exists_pow_eq_one_of_mem_fixedPoints [NeZero p] (hp1 : 1 < p) (x : ProdOne G p)
    (hx : x ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) (ProdOne G p)) :
    ∃ g : G, x.1 = List.replicate p g ∧ g ^ p = 1 := by
  haveI : Fact (1 < p) := ⟨hp1⟩
  have hrot : x.1.rotate 1 = x.1 := by
    have := hx (Multiplicative.ofAdd (1 : ZMod p))
    have h2 := congrArg Subtype.val this
    rw [smul_val] at h2
    simpa [ZMod.val_one] using h2
  obtain ⟨g, hg⟩ := List.rotate_one_eq_self_iff_eq_replicate.mp hrot
  rw [x.2.1] at hg
  refine ⟨g, hg, ?_⟩
  have := x.2.2
  rw [hg, List.prod_replicate] at this
  exact this

end ProdOne

/-- **Key intermediate lemma** (McKay's argument). If a prime `p` divides the order of a finite
group `G`, then `G` contains a nontrivial element `g` satisfying `g ^ p = 1`. -/
theorem exists_ne_one_pow_prime_eq_one
    (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) :
    ∃ g : G, g ≠ 1 ∧ g ^ p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set A := Multiplicative (ZMod p)
  -- `A` is a `p`-group of order `p`
  have hA : IsPGroup p A := by
    refine IsPGroup.of_card (n := 1) ?_
    simp [A, Nat.card_eq_fintype_card, ZMod.card]
  -- the number of length-`p` lists with product one is divisible by `p`
  have hcard : p ∣ Nat.card (ProdOne G p) := by
    rw [ProdOne.card_eq hp.pos]
    exact dvd_pow hdvd (by have := hp.one_lt; omega)
  -- hence so is the number of fixed points
  have hmod : Nat.card (ProdOne G p) ≡
      Nat.card (MulAction.fixedPoints A (ProdOne G p)) [MOD p] :=
    hA.card_modEq_card_fixedPoints (ProdOne G p)
  have hfix : p ∣ Nat.card (MulAction.fixedPoints A (ProdOne G p)) := by
    have := (Nat.modEq_zero_iff_dvd.mpr hcard).symm.trans hmod
    exact (Nat.modEq_zero_iff_dvd).mp this.symm
  -- the fixed points form a nonempty finite set, so there are at least `p ≥ 2` of them
  haveI : Nonempty (MulAction.fixedPoints A (ProdOne G p)) :=
    ⟨⟨ProdOne.trivialVec G p, ProdOne.trivialVec_mem_fixedPoints⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints A (ProdOne G p)) :=
    Nat.card_pos
  have hlt : 1 < Nat.card (MulAction.fixedPoints A (ProdOne G p)) := by
    rcases hfix with ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp [hc] at hpos
    calc 1 < p := hp.one_lt
      _ ≤ p * c := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc0)
      _ = _ := hc.symm
  haveI : Nontrivial (MulAction.fixedPoints A (ProdOne G p)) :=
    Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨y, hy⟩ := exists_ne (⟨ProdOne.trivialVec G p, ProdOne.trivialVec_mem_fixedPoints⟩ :
    MulAction.fixedPoints A (ProdOne G p))
  obtain ⟨g, hgrep, hgpow⟩ :=
    ProdOne.exists_pow_eq_one_of_mem_fixedPoints hp.one_lt y.1 y.2
  refine ⟨g, ?_, hgpow⟩
  rintro rfl
  apply hy
  apply Subtype.ext
  apply ProdOne.ext
  rw [hgrep]
  rfl

/-- **Cauchy's theorem.** If a prime `p` divides the cardinality of a finite group `G`,
then `G` has an element of order exactly `p`. -/
theorem cauchy_group
    (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p := by
  obtain ⟨g, hg1, hgp⟩ := exists_ne_one_pow_prime_eq_one G p hp hdvd
  refine ⟨g, ?_⟩
  have hdvd' : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd') with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg1
  · exact h

end Math

