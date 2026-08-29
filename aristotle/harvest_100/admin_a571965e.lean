import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Betrothed (quasi-amicable) numbers are pairs `m ≠ n` of positive integers with
`s(m) = n + 1` and `s(n) = m + 1`, where `s` is the sum-of-proper-divisors function;
equivalently `σ(m) = σ(n) = m + n + 1`.  Pollack proved that the set of betrothed
numbers has asymptotic density zero.  This file does *not* claim that theorem.  It
delivers a **reduction**: the density-zero statement for betrothed numbers follows
from the density-zero statement for the (much simpler to describe, purely
`σ`-theoretic) set

`SmallerCandidates = {n | 2 * n + 2 ≤ σ(n) ∧ σ(σ(n) - n - 1) = σ(n)}`,

which contains exactly the *smaller* members of betrothed pairs.  The point of the
reduction is that one only ever has to treat the smaller member of a pair, and that
one may forget the pair structure entirely and work with the single arithmetic
condition above.

## Dependency graph

```
                       sigmaOne, Partner, Betrothed, partner        (definitions)
                                     |
              +----------------------+-----------------------+
              |                      |                       |
      Partner.symm            partner_eq_of_partner     Betrothed.pos
              |                      |
              +----------+-----------+
                         |
              Betrothed.partner_spec  --->  Betrothed.partner_ne
                         |                            |
              Betrothed.betrothed_partner             |
                         |                            |
              Betrothed.partner_partner  <------------+
                         |
     +-------------------+--------------------+
     |                                        |
 smallerSet_subset                 card_betrothed_le_two_mul   <--- (Finset injection)
     |                                        |
     +-------------------+--------------------+
                         |
      hasDensityZero_of_card_le (generic analytic lemma)
                         |
              density_zero_reduction          <-- TARGET
```

The two *reusable* analytic-number-theory lemmas isolated here are

* `Brockian.BetrothedNumbers.hasDensityZero_of_card_le` : if the counting function of a
  set is bounded by a constant multiple of the counting function of a density-zero set,
  the set has density zero;
* `Brockian.BetrothedNumbers.card_betrothed_le_two_mul` : the counting function of the
  betrothed numbers is at most twice the counting function of `SmallerCandidates`
  (an involution/injection argument, no analysis).

The remaining, genuinely analytic, input — density zero of `SmallerCandidates`, i.e. the
Erdős–Pollack estimate — is left as an explicit hypothesis and is *not* proved here.
-/

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

namespace Brockian.BetrothedNumbers

/-! ### Basic definitions -/

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `Partner m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: `m` and `n` are
distinct positive integers whose proper-divisor sums satisfy `s(m) = n + 1`, `s(n) = m + 1`,
equivalently `σ(m) = σ(n) = m + n + 1`. -/
def Partner (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- A betrothed (quasi-amicable) number: one that belongs to some betrothed pair. -/
def Betrothed (n : ℕ) : Prop := ∃ m, Partner m n

/-- The candidate partner of `n`, namely `s(n) - 1 = σ(n) - n - 1`.  For a betrothed number
this is the actual (unique) partner. -/
def partner (n : ℕ) : ℕ := sigmaOne n - n - 1

/-- The set of numbers satisfying the purely `σ`-theoretic condition obeyed by the *smaller*
member of every betrothed pair. -/
def SmallerCandidates : Set ℕ :=
  {n | 2 * n + 2 ≤ sigmaOne n ∧ sigmaOne (sigmaOne n - n - 1) = sigmaOne n}

/-- `S` has asymptotic density zero. -/
def HasDensityZero (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun x : ℕ => (((Finset.range x).filter (· ∈ S)).card : ℝ) / (x : ℝ))
    Filter.atTop (nhds 0)

/-! ### Non-vacuity -/

theorem partner_48_75 : Partner 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

theorem betrothed_75 : Betrothed 75 := ⟨48, partner_48_75⟩

theorem betrothed_48 : Betrothed 48 := ⟨75, by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide⟩

/-! ### Structure of betrothed pairs -/

theorem Partner.symm {m n : ℕ} (h : Partner m n) : Partner n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩ <;> omega

theorem Partner.pos_left {m n : ℕ} (h : Partner m n) : 0 < m := h.1

theorem Partner.pos_right {m n : ℕ} (h : Partner m n) : 0 < n := h.2.1

/-- The partner of a betrothed number is determined by it. -/
theorem partner_eq_of_partner {m n : ℕ} (h : Partner m n) : partner n = m := by
  have h2 : sigmaOne n = m + n + 1 := h.2.2.2.2
  unfold partner
  omega

theorem Betrothed.partner_spec {n : ℕ} (h : Betrothed n) : Partner (partner n) n := by
  obtain ⟨m, hm⟩ := h
  rw [partner_eq_of_partner hm]
  exact hm

theorem Betrothed.pos {n : ℕ} (h : Betrothed n) : 0 < n := h.partner_spec.pos_right

theorem Betrothed.partner_ne {n : ℕ} (h : Betrothed n) : partner n ≠ n :=
  h.partner_spec.2.2.1

/-- Betrothedness is inherited by the partner. -/
theorem Betrothed.betrothed_partner {n : ℕ} (h : Betrothed n) : Betrothed (partner n) :=
  ⟨n, h.partner_spec.symm⟩

/-- `partner` is an involution on betrothed numbers. -/
theorem Betrothed.partner_partner {n : ℕ} (h : Betrothed n) : partner (partner n) = n :=
  partner_eq_of_partner h.partner_spec.symm

theorem Betrothed.sigmaOne_eq {n : ℕ} (h : Betrothed n) :
    sigmaOne n = partner n + n + 1 := h.partner_spec.2.2.2.2

/-- The smaller member of a betrothed pair is abundant, and satisfies the defining
`σ`-condition of `SmallerCandidates`. -/
theorem mem_smallerCandidates_of_lt_partner {n : ℕ} (h : Betrothed n) (hlt : n < partner n) :
    n ∈ SmallerCandidates := by
  have hs : sigmaOne n = partner n + n + 1 := h.sigmaOne_eq
  have hp : partner n = sigmaOne n - n - 1 := rfl
  constructor
  · omega
  · rw [← hp, h.partner_spec.symm.2.2.2.2]
    omega

/-! ### The counting reduction -/

/-- The number of betrothed numbers below `x` is at most twice the number of elements of
`SmallerCandidates` below `x`.  (Every betrothed number is either the smaller member of its
pair — and then lies in `SmallerCandidates` — or the larger one, in which case its partner
is a smaller element of `SmallerCandidates`; the involution `partner` makes the second
assignment injective.) -/
theorem card_betrothed_le_two_mul (x : ℕ) :
    ((Finset.range x).filter (fun n => Betrothed n)).card
      ≤ 2 * ((Finset.range x).filter (fun n => n ∈ SmallerCandidates)).card := by
  classical
  have hsplit :
      (((Finset.range x).filter (fun n => Betrothed n)).filter
            (fun n => n < partner n)).card
        + (((Finset.range x).filter (fun n => Betrothed n)).filter
            (fun n => ¬ n < partner n)).card
        = ((Finset.range x).filter (fun n => Betrothed n)).card :=
    Finset.card_filter_add_card_filter_not _
  have hmem : ∀ n : ℕ, n ∈ ((Finset.range x).filter (fun n => Betrothed n)).filter
      (fun n => n < partner n) ↔ (n < x ∧ Betrothed n ∧ n < partner n) := by
    intro n
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  have hmem' : ∀ n : ℕ, n ∈ ((Finset.range x).filter (fun n => Betrothed n)).filter
      (fun n => ¬ n < partner n) ↔ (n < x ∧ Betrothed n ∧ ¬ n < partner n) := by
    intro n
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  have h1 : (((Finset.range x).filter (fun n => Betrothed n)).filter
      (fun n => n < partner n)) ⊆ (Finset.range x).filter (fun n => n ∈ SmallerCandidates) := by
    intro n hn
    rw [hmem] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hn.1, mem_smallerCandidates_of_lt_partner hn.2.1 hn.2.2⟩
  have h2 : (((Finset.range x).filter (fun n => Betrothed n)).filter
        (fun n => ¬ n < partner n)).card
      ≤ (((Finset.range x).filter (fun n => Betrothed n)).filter
        (fun n => n < partner n)).card := by
    refine Finset.card_le_card_of_injOn partner ?_ ?_
    · intro n hn
      rw [Finset.mem_coe, hmem'] at hn
      obtain ⟨hnx, hb, hle⟩ := hn
      have hne : partner n ≠ n := hb.partner_ne
      have hlt : partner n < n := by omega
      rw [Finset.mem_coe, hmem]
      refine ⟨by omega, hb.betrothed_partner, ?_⟩
      rw [hb.partner_partner]
      exact hlt
    · intro a ha b hb hab
      rw [Finset.mem_coe, hmem'] at ha hb
      have ha' := ha.2.1.partner_partner
      have hb' := hb.2.1.partner_partner
      rw [← ha', ← hb', hab]
  have h3 := Finset.card_le_card h1
  omega

/-! ### Abundancy of the two members of a pair -/

/-- The smaller member of a betrothed pair is abundant. -/
theorem Betrothed.abundant_of_lt_partner {n : ℕ} (h : Betrothed n) (hlt : n < partner n) :
    2 * n + 2 ≤ sigmaOne n := by
  have hs : sigmaOne n = partner n + n + 1 := h.sigmaOne_eq
  omega

/-- The larger member of a betrothed pair is not abundant. -/
theorem Betrothed.not_abundant_of_partner_lt {n : ℕ} (h : Betrothed n) (hlt : partner n < n) :
    sigmaOne n ≤ 2 * n := by
  have hs : sigmaOne n = partner n + n + 1 := h.sigmaOne_eq
  omega

/-! ### Reusable analytic lemmas -/

/-! #### The main counting-to-density lemma -/

/-- If the counting function of `S` is bounded by `c` times the counting function of a set
`T` of density zero, then `S` has density zero. -/
theorem hasDensityZero_of_card_le {S T : Set ℕ} (c : ℕ) (hT : HasDensityZero T)
    (h : ∀ x : ℕ, ((Finset.range x).filter (· ∈ S)).card
        ≤ c * ((Finset.range x).filter (· ∈ T)).card) :
    HasDensityZero S := by
  classical
  have hmain : Filter.Tendsto
      (fun x : ℕ => (c : ℝ) * ((((Finset.range x).filter (· ∈ T)).card : ℝ) / (x : ℝ)))
      Filter.atTop (nhds 0) := by
    have := hT.const_mul (c : ℝ)
    simpa using this
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) hmain
  have key : (c : ℝ) * ((((Finset.range x).filter (· ∈ T)).card : ℝ) / (x : ℝ))
      = ((c * ((Finset.range x).filter (· ∈ T)).card : ℕ) : ℝ) / (x : ℝ) := by
    push_cast
    ring
  rw [key]
  gcongr
  exact_mod_cast h x

/-- A subset of a density-zero set has density zero. -/
theorem HasDensityZero.subset {S T : Set ℕ} (hT : HasDensityZero T) (hST : S ⊆ T) :
    HasDensityZero S := by
  classical
  refine hasDensityZero_of_card_le 1 hT (fun x => ?_)
  rw [one_mul]
  refine Finset.card_le_card (fun n hn => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

/-- A union of two density-zero sets has density zero. -/
theorem HasDensityZero.union {S T : Set ℕ} (hS : HasDensityZero S) (hT : HasDensityZero T) :
    HasDensityZero (S ∪ T) := by
  classical
  have h : Filter.Tendsto
      (fun x : ℕ => ((((Finset.range x).filter (· ∈ S)).card : ℝ) / (x : ℝ))
        + ((((Finset.range x).filter (· ∈ T)).card : ℝ) / (x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hS.add hT
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) h
  have hcard : ((Finset.range x).filter (· ∈ S ∪ T)).card
      ≤ ((Finset.range x).filter (· ∈ S)).card + ((Finset.range x).filter (· ∈ T)).card := by
    have hsub : (Finset.range x).filter (· ∈ S ∪ T)
        ⊆ ((Finset.range x).filter (· ∈ S)) ∪ ((Finset.range x).filter (· ∈ T)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Set.mem_union] at hn ⊢
      tauto
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hx : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  rw [div_add_div_same]
  gcongr
  exact_mod_cast hcard

/-- A finite set has density zero. -/
theorem hasDensityZero_of_finite {S : Set ℕ} (hS : S.Finite) : HasDensityZero S := by
  classical
  have hb : ∀ x : ℕ, ((Finset.range x).filter (· ∈ S)).card ≤ hS.toFinset.card := by
    intro x
    refine Finset.card_le_card (fun n hn => ?_)
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact hS.mem_toFinset.2 hn.2
  refine squeeze_zero (fun x => by positivity) (fun x => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (hS.toFinset.card : ℝ))
  have hx : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  gcongr
  exact_mod_cast hb x

/-! ### The target reduction -/

/-- **Density zero reduction for betrothed numbers.**

If the set `{n | 2n + 2 ≤ σ(n) ∧ σ(σ(n) - n - 1) = σ(n)}` — which contains every smaller
member of a betrothed pair — has asymptotic density zero, then the set of betrothed
(quasi-amicable) numbers has asymptotic density zero.

This is the reduction step in Pollack's theorem; the density-zero statement for
`SmallerCandidates` is the remaining analytic input and is *not* proved here. -/
theorem density_zero_reduction (h : HasDensityZero SmallerCandidates) :
    HasDensityZero {n | Betrothed n} :=
  hasDensityZero_of_card_le 2 h (fun x => card_betrothed_le_two_mul x)

end Brockian.BetrothedNumbers

