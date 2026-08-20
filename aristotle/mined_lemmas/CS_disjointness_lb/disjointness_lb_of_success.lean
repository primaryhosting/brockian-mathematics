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

theorem disjointness_lb_of_success {n c : ℕ} {R : Type} [Fintype R] {δ : ℝ}
    (w : R → ℝ) (hw0 : ∀ r, 0 ≤ w r) (hw1 : ∑ r, w r = 1)
    (P : R → Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hcost : ∀ r, (P r).cost ≤ c)
    (hsound : ∀ r x y, (P r).run x y = true → Disjoint x y)
    (hsucc : ∀ x y : Finset (Fin n), Disjoint x y →
      δ ≤ ∑ r ∈ Finset.univ.filter (fun r => (P r).run x y = true), w r) :
    δ * 2 ^ n ≤ 2 ^ c := by
  classical
  set A : R → Finset (Finset (Fin n)) :=
    fun r => Finset.univ.filter (fun x => (P r).run x xᶜ = true) with hA
  -- each seed accepts at most `2 ^ c` complementary pairs `(x, xᶜ)`
  have hAcard : ∀ r, (A r).card ≤ 2 ^ c := by
    intro r
    have himg : ((A r).image (fun x : Finset (Fin n) => (x, xᶜ))).card ≤ 2 ^ (P r).cost := by
      refine Protocol.card_fooling_le (P r) _ ?_ ?_
      · intro p hp
        simp only [Finset.mem_image] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        rw [hA] at hx
        simpa using (Finset.mem_filter.1 hx).2
      · intro p hp q hq hne
        simp only [Finset.mem_image] at hp hq
        obtain ⟨x, _, rfl⟩ := hp
        obtain ⟨z, _, rfl⟩ := hq
        have hxz : x ≠ z := fun h => hne (by rw [h])
        rcases cross_not_disjoint hxz with h | h
        · refine Or.inl ?_
          by_contra hcon
          exact h (hsound r x zᶜ (by simpa using hcon))
        · refine Or.inr ?_
          by_contra hcon
          exact h (hsound r z xᶜ (by simpa using hcon))
    have hinj : ((A r).image (fun x : Finset (Fin n) => (x, xᶜ))).card = (A r).card :=
      Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab)
    rw [hinj] at himg
    exact himg.trans (Nat.pow_le_pow_right (by norm_num) (hcost r))
  -- upper bound on the average number of accepted complementary pairs
  have hupper : ∑ r, w r * ((A r).card : ℝ) ≤ 2 ^ c := by
    have hterm : ∀ r ∈ (Finset.univ : Finset R), w r * ((A r).card : ℝ) ≤ w r * 2 ^ c := by
      intro r _
      have : ((A r).card : ℝ) ≤ (2:ℝ) ^ c := by exact_mod_cast hAcard r
      exact mul_le_mul_of_nonneg_left this (hw0 r)
    calc ∑ r, w r * ((A r).card : ℝ) ≤ ∑ r, w r * 2 ^ c := Finset.sum_le_sum hterm
      _ = (∑ r, w r) * 2 ^ c := by rw [← Finset.sum_mul]
      _ = 2 ^ c := by rw [hw1, one_mul]
  -- lower bound via double counting: every complementary pair is accepted with probability ≥ δ
  have hlower : δ * 2 ^ n ≤ ∑ r, w r * ((A r).card : ℝ) := by
    have hswap : ∑ r, w r * ((A r).card : ℝ)
        = ∑ x : Finset (Fin n), ∑ r, (if (P r).run x xᶜ = true then w r else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro r _
      rw [hA, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hswap]
    have hx : ∀ x : Finset (Fin n),
        δ ≤ ∑ r, (if (P r).run x xᶜ = true then w r else 0) := by
      intro x
      have := hsucc x xᶜ disjoint_compl_right
      rwa [Finset.sum_filter] at this
    calc δ * 2 ^ n
        = ∑ _x : Finset (Fin n), δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
          rw [nsmul_eq_mul, mul_comm]
          norm_cast
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hx x)
  exact le_trans hlower hupper

/-- **Ω(n) lower bound for randomized set disjointness (one-sided error).**

Any public-coin randomized protocol for set disjointness on subsets of an `n`-element universe
which never answers "disjoint" on an intersecting pair (perfect soundness) and answers
"disjoint" with probability at least `1/2` on every disjoint pair must have communication cost
at least `n - 1`; in particular set disjointness requires `Ω(n)` bits of randomized
communication. -/
