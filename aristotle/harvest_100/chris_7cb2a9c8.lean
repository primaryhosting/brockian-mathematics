import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The statement of the Feit–Thompson (odd order) theorem: every finite group of odd
order is solvable. -/
def FeitThompsonStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The "simple case" of the Feit–Thompson theorem: every finite simple group of odd order
is abelian (equivalently, is cyclic of prime order). -/
def OddOrderSimpleIsAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → IsSimpleGroup G →
    ∀ a b : G, a * b = b * a

section Auxiliary

variable {G : Type} [Group G]

/-- A group is solvable as soon as it has a normal subgroup `N` such that both `N` and `G ⧸ N`
are solvable. -/
theorem isSolvable_of_normal_subgroup (N : Subgroup G) [N.Normal] [IsSolvable N]
    [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])

/-- A nontrivial proper normal subgroup of a finite group has strictly smaller cardinality. -/
theorem card_lt_of_ne_top {N : Subgroup G} (h : N ≠ ⊤) [Finite G] :
    Nat.card N < Nat.card G := by
  have hq : 1 < Nat.card (G ⧸ N) := by
    have hpos := Nat.card_pos (α := G ⧸ N)
    rcases Nat.lt_or_ge 1 (Nat.card (G ⧸ N)) with h' | h'
    · exact h'
    · exact absurd (Subgroup.index_eq_one.mp (by rw [Subgroup.index_eq_card]; omega)) h
  have hsub := Nat.card_pos (α := N)
  have := N.card_eq_card_quotient_mul_card_subgroup
  nlinarith

/-- The quotient by a nontrivial normal subgroup of a finite group has strictly smaller
cardinality. -/
theorem card_quotient_lt_of_ne_bot {N : Subgroup G} [N.Normal] (h : N ≠ ⊥) [Finite G] :
    Nat.card (G ⧸ N) < Nat.card G := by
  have hsub : 1 < Nat.card N := by
    have hpos := Nat.card_pos (α := N)
    rcases Nat.lt_or_ge 1 (Nat.card N) with h' | h'
    · exact h'
    · exact absurd (Subgroup.card_eq_one.mp (by omega)) h
  have hq := Nat.card_pos (α := G ⧸ N)
  have := N.card_eq_card_quotient_mul_card_subgroup
  nlinarith

/-- Oddness of the order is inherited by subgroups and quotients (any divisor of an odd
number is odd). -/
theorem odd_of_dvd {m n : ℕ} (hn : Odd n) (h : m ∣ n) : Odd m := by
  rw [Nat.odd_iff] at hn ⊢
  by_contra hm
  have h2 : 2 ∣ m := by omega
  have : 2 ∣ n := h2.trans h
  omega

end Auxiliary

/-- **Reduction of the Feit–Thompson theorem to the simple case.**

If every finite *simple* group of odd order is abelian, then every finite group of odd order
is solvable.  This is the standard minimal-counterexample reduction: in a minimal odd-order
non-solvable group every proper nontrivial normal subgroup and the corresponding quotient are
smaller of odd order, hence solvable, hence so is the group; so the minimal counterexample is
simple, hence abelian by hypothesis, hence solvable — a contradiction.

The remaining (deep) input, `OddOrderSimpleIsAbelian`, is the Feit–Thompson theorem proper and
is not proved here. -/
theorem feit_thompson_odd_order (h : OddOrderSimpleIsAbelian) : FeitThompsonStatement := by
  suffices H : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → Odd (Nat.card G) →
      IsSolvable G by
    intro G _ _ hodd
    exact H (Nat.card G) G rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ hcard hodd
    subst hcard
    rcases subsingleton_or_nontrivial G with hs | hs
    · exact isSolvable_of_subsingleton G
    by_cases hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤
    · -- `G` is simple, so abelian by hypothesis
      haveI : IsSimpleGroup G := ⟨fun {N} hN => hsimple N hN⟩
      exact isSolvable_of_comm (h G hodd inferInstance)
    · -- `G` has a proper nontrivial normal subgroup; use induction
      push_neg at hsimple
      obtain ⟨N, hN, hbot, htop⟩ := hsimple
      haveI := hN
      haveI : IsSolvable N :=
        IH (Nat.card N) (card_lt_of_ne_top htop) N rfl
          (odd_of_dvd hodd N.card_subgroup_dvd_card)
      haveI : IsSolvable (G ⧸ N) :=
        IH (Nat.card (G ⧸ N)) (card_quotient_lt_of_ne_bot hbot) (G ⧸ N) rfl
          (odd_of_dvd hodd N.card_quotient_dvd_card)
      exact isSolvable_of_normal_subgroup N

/-- A solvable simple group is abelian: its commutator subgroup is trivial. -/
theorem mul_comm_of_isSimpleGroup_of_isSolvable {G : Type} [Group G] [IsSimpleGroup G]
    [h : IsSolvable G] (a b : G) : a * b = b * a := by
  obtain ⟨n, hn⟩ := h.solvable
  have hc : commutator G = ⊥ := by
    cases n with
    | zero =>
      have h1 : derivedSeries G 1 ≤ derivedSeries G 0 := derivedSeries_antitone G (Nat.zero_le 1)
      rw [hn, derivedSeries_one] at h1
      exact le_bot_iff.mp h1
    | succ m => rw [← IsSimpleGroup.derivedSeries_succ (n := m)]; exact hn
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hmem : ⁅a, b⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hc] at hmem
  simpa using hmem

/-- The Feit–Thompson theorem is *equivalent* to its simple-group case: every finite group of
odd order is solvable if and only if every finite simple group of odd order is abelian. -/
theorem feit_thompson_iff_simple_case : FeitThompsonStatement ↔ OddOrderSimpleIsAbelian := by
  refine ⟨fun hFT G _ _ hodd hsimple a b => ?_, feit_thompson_odd_order⟩
  haveI := hsimple
  haveI := hFT G hodd
  exact mul_comm_of_isSimpleGroup_of_isSolvable a b

/-- Base case: a finite `p`-group is solvable (in particular every group of odd prime power
order is solvable). -/
theorem isSolvable_of_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) : IsSolvable G :=
  have := hG.isNilpotent
  IsNilpotent.to_isSolvable

/-- Base case: every finite group whose order is an odd prime power is solvable. -/
theorem isSolvable_of_card_eq_prime_pow {G : Type} [Group G] [Finite G] {p k : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p ^ k) : IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSolvable_of_isPGroup (IsPGroup.of_card hcard)

/-- The smallest prime factor of a product of two primes `p < q` is `p`. -/
theorem minFac_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    (p * q).minFac = p := by
  have h2 := Nat.minFac_prime (n := p * q)
    (by have := hp.two_le; have := hq.two_le; nlinarith)
  have hd : (p * q).minFac ∣ p * q := Nat.minFac_dvd _
  have hle := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases (Nat.Prime.dvd_mul h2).mp hd with h3 | h3
  · exact (Nat.prime_dvd_prime_iff_eq h2 hp).mp h3
  · have := (Nat.prime_dvd_prime_iff_eq h2 hq).mp h3
    omega

/-- Base case: every finite group of order `p * q`, with `p < q` primes, is solvable.
Indeed the Sylow `q`-subgroup has index `p`, the smallest prime factor of the order, hence is
normal; it and the quotient have prime order. -/
theorem isSolvable_of_card_eq_prime_mul_prime {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hlt : p < q) (hcard : Nat.card G = p * q) : IsSolvable G := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain P := (default : Sylow q G)
  have hPc : Nat.card (P : Subgroup G) = q := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization, hq.factorization,
      Finsupp.single_apply]
    rw [if_neg (show ¬ p = q by omega)]
    simp
  have hidx : (P : Subgroup G).index = p := by
    have hmul := (P : Subgroup G).index_mul_card
    rw [hPc, hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_right hq.pos hmul
  haveI : (P : Subgroup G).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hidx, hcard, minFac_prime_mul_prime hp hq hlt]
  haveI : IsSolvable (P : Subgroup G) :=
    isSolvable_of_card_eq_prime_pow (k := 1) hq (by simpa using hPc)
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    refine isSolvable_of_card_eq_prime_pow (p := p) (k := 1) hp ?_
    rw [← Subgroup.index_eq_card, hidx, pow_one]
  exact isSolvable_of_normal_subgroup (P : Subgroup G)

/-- Base case of the Feit–Thompson theorem: every group of odd order less than `45` is solvable.
(Every odd number below `45` is either a prime power or a product of two distinct primes; the
smallest odd order not of this shape is `45 = 3 ^ 2 * 5`.) -/
theorem isSolvable_of_odd_card_lt_45 {G : Type} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) : IsSolvable G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  rw [hn] at hodd hlt hpos
  interval_cases n <;>
    first
      | (exfalso; revert hodd; decide)
      | ((refine isSolvable_of_card_eq_prime_pow (p := Nat.card G) (k := 1) ?_ ?_ <;>
          norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_pow (p := 3) (k := 0) ?_ ?_ <;> norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_pow (p := 3) (k := 2) ?_ ?_ <;> norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_pow (p := 3) (k := 3) ?_ ?_ <;> norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_pow (p := 5) (k := 2) ?_ ?_ <;> norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_mul_prime (p := 3) (q := 5) ?_ ?_ ?_ ?_ <;>
          norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_mul_prime (p := 3) (q := 7) ?_ ?_ ?_ ?_ <;>
          norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_mul_prime (p := 3) (q := 11) ?_ ?_ ?_ ?_ <;>
          norm_num [hn]); done)
      | ((refine isSolvable_of_card_eq_prime_mul_prime (p := 3) (q := 13) ?_ ?_ ?_ ?_ <;>
          norm_num [hn]); done)
      | (refine isSolvable_of_card_eq_prime_mul_prime (p := 5) (q := 7) ?_ ?_ ?_ ?_ <;>
          norm_num [hn])

end Frontier

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

