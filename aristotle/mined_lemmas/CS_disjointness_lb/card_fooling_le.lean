import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

We formalize deterministic two-party communication protocols as protocol trees
(`CS.Protocol`), with `CS.Protocol.run` the output and `CS.Protocol.cost` the worst-case number
of exchanged bits, and prove the fooling-set bound `CS.Protocol.card_fooling_le`: a protocol of
cost `c` admits no fooling set of size larger than `2 ^ c`.

Applying it to the fooling set `{(x, xᶜ) : x ⊆ [n]}` for set disjointness gives

* `CS.disjointness_deterministic_lb`: every deterministic protocol computing set disjointness on
  subsets of an `n`-element universe costs at least `n` bits;
* `CS.disjointness_lb_of_success` and `CS.disjointness_lb`: every *public-coin randomized*
  protocol with perfect soundness (it never answers "disjoint" on an intersecting pair) that
  answers "disjoint" with probability at least `1/2` (more generally `δ`) on each disjoint pair
  costs at least `n - 1` bits (more generally `δ * 2 ^ n ≤ 2 ^ c`).  Hence set disjointness has
  `Ω(n)` randomized communication complexity in the one-sided-error model.
* `CS.disjointness_ub`: a matching deterministic protocol of cost `n + 1`, so the bounds are
  tight up to an additive constant and the hypotheses above are satisfiable.

The randomized lower bound proved here is for the one-sided-error (perfectly sound) model; the
two-sided bounded-error case (Kalyanasundaram–Schnitger, Razborov) is not formalized here.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u v

/-- A deterministic two-party communication protocol with Boolean output.
`alice f t e` means Alice sends the bit `f x` and the parties continue with `t` or `e`;
`bob g t e` is the same with Bob speaking. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf (b : Bool) : Protocol X Y
  | alice (f : X → Bool) (t e : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (t e : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem card_fooling_le [DecidableEq X] [DecidableEq Y] :
    ∀ (P : Protocol X Y) (T : Finset (X × Y)),
      (∀ p ∈ T, P.run p.1 p.2 = true) →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → P.run p.1 q.2 = false ∨ P.run q.1 p.2 = false) →
      T.card ≤ 2 ^ P.cost := by
  intro P
  induction P with
  | leaf b =>
      intro T hacc hcross
      have : T.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro p hp q hq
        by_contra hne
        have h1 := hacc p hp
        rcases hcross p hp q hq hne with h | h <;>
          simp [run] at h h1 <;> simp [h1] at h
      simpa [cost] using this
  | alice f t e iht ihe =>
      intro T hacc hcross
      classical
      set T1 : Finset (X × Y) := T.filter (fun p => f p.1 = true) with hT1
      set T0 : Finset (X × Y) := T.filter (fun p => ¬ f p.1 = true) with hT0
      have hcard : T1.card + T0.card = T.card :=
        Finset.card_filter_add_card_filter_not (s := T) (fun p : X × Y => f p.1 = true)
      have h1 : T1.card ≤ 2 ^ t.cost := by
        refine iht T1 ?_ ?_
        · intro p hp
          rw [hT1, Finset.mem_filter] at hp
          have := hacc p hp.1
          rw [run, if_pos hp.2] at this
          exact this
        · intro p hp q hq hne
          rw [hT1, Finset.mem_filter] at hp hq
          have := hcross p hp.1 q hq.1 hne
          rw [run, if_pos hp.2, run, if_pos hq.2] at this
          exact this
      have h0 : T0.card ≤ 2 ^ e.cost := by
        refine ihe T0 ?_ ?_
        · intro p hp
          rw [hT0, Finset.mem_filter] at hp
          have := hacc p hp.1
          rw [run, if_neg hp.2] at this
          exact this
        · intro p hp q hq hne
          rw [hT0, Finset.mem_filter] at hp hq
          have := hcross p hp.1 q hq.1 hne
          rw [run, if_neg hp.2, run, if_neg hq.2] at this
          exact this
      have hle : T.card ≤ 2 ^ t.cost + 2 ^ e.cost := by omega
      have hmax : 2 ^ t.cost + 2 ^ e.cost ≤ 2 ^ (max t.cost e.cost + 1) := by
        have ht : (2:ℕ) ^ t.cost ≤ 2 ^ max t.cost e.cost :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have he : (2:ℕ) ^ e.cost ≤ 2 ^ max t.cost e.cost :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have : (2:ℕ) ^ (max t.cost e.cost + 1) = 2 ^ max t.cost e.cost + 2 ^ max t.cost e.cost := by
          ring
        omega
      simpa [cost] using le_trans hle hmax
  | bob g t e iht ihe =>
      intro T hacc hcross
      classical
      set T1 : Finset (X × Y) := T.filter (fun p => g p.2 = true) with hT1
      set T0 : Finset (X × Y) := T.filter (fun p => ¬ g p.2 = true) with hT0
      have hcard : T1.card + T0.card = T.card :=
        Finset.card_filter_add_card_filter_not (s := T) (fun p : X × Y => g p.2 = true)
      have h1 : T1.card ≤ 2 ^ t.cost := by
        refine iht T1 ?_ ?_
        · intro p hp
          rw [hT1, Finset.mem_filter] at hp
          have := hacc p hp.1
          rw [run, if_pos hp.2] at this
          exact this
        · intro p hp q hq hne
          rw [hT1, Finset.mem_filter] at hp hq
          have := hcross p hp.1 q hq.1 hne
          rw [run, if_pos hq.2, run, if_pos hp.2] at this
          exact this
      have h0 : T0.card ≤ 2 ^ e.cost := by
        refine ihe T0 ?_ ?_
        · intro p hp
          rw [hT0, Finset.mem_filter] at hp
          have := hacc p hp.1
          rw [run, if_neg hp.2] at this
          exact this
        · intro p hp q hq hne
          rw [hT0, Finset.mem_filter] at hp hq
          have := hcross p hp.1 q hq.1 hne
          rw [run, if_neg hq.2, run, if_neg hp.2] at this
          exact this
      have hle : T.card ≤ 2 ^ t.cost + 2 ^ e.cost := by omega
      have hmax : 2 ^ t.cost + 2 ^ e.cost ≤ 2 ^ (max t.cost e.cost + 1) := by
        have ht : (2:ℕ) ^ t.cost ≤ 2 ^ max t.cost e.cost :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have he : (2:ℕ) ^ e.cost ≤ 2 ^ max t.cost e.cost :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have : (2:ℕ) ^ (max t.cost e.cost + 1) = 2 ^ max t.cost e.cost + 2 ^ max t.cost e.cost := by
          ring
        omega
      simpa [cost] using le_trans hle hmax

end Protocol

/-- The set-disjointness function on `n`-element ground set. -/
