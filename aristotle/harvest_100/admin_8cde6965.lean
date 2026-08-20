/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

universe u

/-- The full Feit–Thompson theorem, as a proposition about a universe of types:
every finite group of odd order is solvable. -/
def FeitThompsonStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The "hard core" of the Feit–Thompson theorem: every finite *simple* group of odd
order is cyclic (equivalently, of prime order). -/
def OddOrderSimpleIsCyclic : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSimpleGroup G → IsCyclic G

/-- A divisor of an odd number is odd. -/
theorem odd_of_dvd_odd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m := by
  obtain ⟨k, rfl⟩ := hmn
  exact (Nat.odd_mul.mp hn).1

/-- A nontrivial group that is not simple has a normal subgroup that is neither trivial
nor everything. -/
theorem exists_proper_normal_of_not_simple {G : Type u} [Group G] [Nontrivial G]
    (h : ¬ IsSimpleGroup G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  exact h { exists_pair_ne := exists_pair_ne G
            eq_bot_or_eq_top_of_normal := fun N hN => by
              by_cases hb : N = ⊥
              · exact Or.inl hb
              · exact Or.inr (hc N hN hb) }

/-- A cyclic group is solvable. -/
theorem isSolvable_of_isCyclic {G : Type u} [Group G] [IsCyclic G] : IsSolvable G :=
  isSolvable_of_comm (fun a b => (IsCyclic.commGroup (α := G)).mul_comm a b)

/-- **Feit–Thompson, reduced to the simple case.**  Granting `OddOrderSimpleIsCyclic`, i.e. that
every finite simple group of odd order is cyclic (the deep content of the Feit–Thompson theorem),
every finite group of odd order is solvable.  This is the standard induction on the order:
a minimal counterexample would have to be simple. -/
theorem feit_thompson_odd_order (h : OddOrderSimpleIsCyclic.{u}) :
    FeitThompsonStatement.{u} := by
  intro G _ _ hodd
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    subst hn
    rcases subsingleton_or_nontrivial G with hs | hs
    · infer_instance
    by_cases hsimple : IsSimpleGroup G
    · have : IsCyclic G := h G hodd hsimple
      exact isSolvable_of_isCyclic
    · obtain ⟨N, hN, hbot, htop⟩ := exists_proper_normal_of_not_simple hsimple
      have hmul : Nat.card N * Nat.card (G ⧸ N) = Nat.card G := Subgroup.card_mul_index N
      have hNgt : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hbot
      have hQgt : 1 < Nat.card (G ⧸ N) := by
        have : N.index ≠ 1 := fun hi => htop (Subgroup.index_eq_one.mp hi)
        have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
        have : Nat.card (G ⧸ N) ≠ 1 := this
        omega
      have hNdvd : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
      have hQdvd : Nat.card (G ⧸ N) ∣ Nat.card G := ⟨Nat.card N, by rw [← hmul]; ring⟩
      have hNlt : Nat.card N < Nat.card G := by nlinarith [Nat.card_pos (α := N)]
      have hQlt : Nat.card (G ⧸ N) < Nat.card G := by
        nlinarith [Nat.card_pos (α := G ⧸ N)]
      have hsolN : IsSolvable N := ih _ hNlt N (odd_of_dvd_odd hNdvd hodd) rfl
      have hsolQ : IsSolvable (G ⧸ N) := ih _ hQlt (G ⧸ N) (odd_of_dvd_odd hQdvd hodd) rfl
      exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-! ### Unconditional base cases

The reduction above is conditional on the deep simple-group input.  The following results are
unconditional special cases of the Feit–Thompson theorem. -/

/-- Any finite `p`-group is solvable (via nilpotency). -/
theorem isSolvable_of_card_eq_prime_pow {G : Type u} [Group G] [Finite G] {p k : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p ^ k) : IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card hcard
  haveI : Group.IsNilpotent G := hpg.isNilpotent
  infer_instance

/-- A group of order `p * q`, with `p < q` primes, is solvable: its Sylow `q`-subgroup is
normal, and both it and the quotient are cyclic of prime order. -/
theorem isSolvable_of_card_eq_prime_mul_prime {G : Type u} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hcard : Nat.card G = p * q) : IsSolvable G := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain Q : Sylow q G := default
  have hne : p ≠ q := hpq.ne
  have hQcard : Nat.card (Q : Subgroup G) = q := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp [hp.factorization, hq.factorization, hne]
  have hindex : (Q : Subgroup G).index = p := by
    have hmul := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hQcard, hcard] at hmul
    have hq0 : 0 < q := hq.pos
    nlinarith [hmul]
  have hn : Nat.card (Sylow q G) = 1 := by
    have hdvd : Nat.card (Sylow q G) ∣ p := hindex ▸ Sylow.card_dvd_index Q
    rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h1 | h1
    · exact h1
    · exfalso
      have hmod := card_sylow_modEq_one q G
      rw [h1] at hmod
      have h2 : p % q = p := Nat.mod_eq_of_lt hpq
      have h3 : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
      have h4 : p % q = 1 % q := hmod
      have h5 := hp.one_lt
      omega
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hn).1
  haveI : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  haveI : IsCyclic (Q : Subgroup G) := isCyclic_of_prime_card hQcard
  haveI : IsSolvable (Q : Subgroup G) := isSolvable_of_isCyclic
  haveI : IsCyclic (G ⧸ (Q : Subgroup G)) := isCyclic_of_prime_card (p := p) hindex
  haveI : IsSolvable (G ⧸ (Q : Subgroup G)) := isSolvable_of_isCyclic
  exact solvable_of_ker_le_range (Q : Subgroup G).subtype (QuotientGroup.mk' (Q : Subgroup G))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- Every odd number below `45` is either a prime power or a product of two distinct primes. -/
theorem odd_lt_45_prime_pow_or_prime_mul_prime :
    ∀ n < 45, Odd n →
      ((∃ p ≤ 45, ∃ k ≤ 6, Nat.Prime p ∧ n = p ^ k) ∨
        (∃ p ≤ 45, ∃ q ≤ 45, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p * q)) := by
  decide

/-- **Unconditional base case of Feit–Thompson**: every finite group of odd order less
than `45` is solvable.  (`45 = 3 ^ 2 * 5` is the first odd order that is neither a prime power
nor a product of two distinct primes.) -/
theorem isSolvable_of_odd_card_lt_45 {G : Type u} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) : IsSolvable G := by
  rcases odd_lt_45_prime_pow_or_prime_mul_prime _ hlt hodd with
    ⟨p, -, k, -, hp, hcard⟩ | ⟨p, -, q, -, hp, hq, hpq, hcard⟩
  · exact isSolvable_of_card_eq_prime_pow hp hcard
  · exact isSolvable_of_card_eq_prime_mul_prime hp hq hpq hcard

end Frontier

