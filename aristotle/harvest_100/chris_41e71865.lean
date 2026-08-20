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
def run : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice f t e, x, y => if f x then run t x y else run e x y
  | bob g t e, x, y => if g y then run t x y else run e x y

/-- The communication cost (worst-case number of exchanged bits) of a protocol. -/
def cost : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ t e => max (cost t) (cost e) + 1
  | bob _ t e => max (cost t) (cost e) + 1

/-- **Fooling set bound.** If `T` is a set of input pairs that the protocol accepts, and for
any two distinct pairs in `T` one of the two "crossed" pairs is rejected, then `T` has at most
`2 ^ cost` elements (a protocol of cost `c` has at most `2 ^ c` leaves, and each leaf gives a
combinatorial rectangle). -/
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
def Disj (n : ℕ) (x y : Finset (Fin n)) : Bool := decide (Disjoint x y)

/-- The complementation fooling set `{(x, xᶜ)}` for set disjointness: the pairs are disjoint,
and for `x ≠ z` at least one of `(x, zᶜ)`, `(z, xᶜ)` is intersecting. -/
theorem cross_not_disjoint {n : ℕ} {x z : Finset (Fin n)} (h : x ≠ z) :
    ¬ Disjoint x zᶜ ∨ ¬ Disjoint z xᶜ := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  exact h (subset_antisymm (Finset.subset_iff.2 fun a ha => by
      by_contra hz
      exact (Finset.disjoint_left.1 h1 ha) (Finset.mem_compl.2 hz))
    (Finset.subset_iff.2 fun a ha => by
      by_contra hx
      exact (Finset.disjoint_left.1 h2 ha) (Finset.mem_compl.2 hx)))

/-- **Deterministic lower bound.** Any deterministic protocol computing set disjointness on
subsets of an `n`-element universe must communicate at least `n` bits. -/
theorem disjointness_deterministic_lb {n : ℕ} (P : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hP : ∀ x y, P.run x y = Disj n x y) : n ≤ P.cost := by
  classical
  have hT : (Finset.univ.image (fun x : Finset (Fin n) => (x, xᶜ))).card ≤ 2 ^ P.cost := by
    refine Protocol.card_fooling_le P _ ?_ ?_
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨x, rfl⟩ := hp
      simp [hP, Disj, disjoint_compl_right]
    · intro p hp q hq hne
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨x, rfl⟩ := hp
      obtain ⟨z, rfl⟩ := hq
      have hxz : x ≠ z := by
        intro h; exact hne (by rw [h])
      rcases cross_not_disjoint hxz with h | h
      · exact Or.inl (by simp [hP, Disj, h])
      · exact Or.inr (by simp [hP, Disj, h])
  have hcard : (Finset.univ.image (fun x : Finset (Fin n) => (x, xᶜ))).card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab)]
    simp [Fintype.card_finset]
  rw [hcard] at hT
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hT

/-- The trivial protocol in which Alice reveals membership in `x` of each element of the list
`L` (accumulating the revealed elements of `x` in `a`), after which Bob announces the answer. -/
def reveal {n : ℕ} : List (Fin n) → Finset (Fin n) → Protocol (Finset (Fin n)) (Finset (Fin n))
  | [], a => Protocol.bob (fun y => decide (Disjoint a y)) (Protocol.leaf true)
      (Protocol.leaf false)
  | i :: L, a => Protocol.alice (fun x => decide (i ∈ x)) (reveal L (insert i a)) (reveal L a)

theorem reveal_cost {n : ℕ} (L : List (Fin n)) (a : Finset (Fin n)) :
    (reveal L a).cost = L.length + 1 := by
  induction L generalizing a with
  | nil => simp [reveal, Protocol.cost]
  | cons i L ih => simp [reveal, Protocol.cost, ih]

theorem reveal_run {n : ℕ} (L : List (Fin n)) (hL : L.Nodup) (a x y : Finset (Fin n))
    (hinv : ∀ j : Fin n, j ∈ a ↔ (j ∈ x ∧ j ∉ L)) :
    (reveal L a).run x y = Disj n x y := by
  induction L generalizing a with
  | nil =>
      have hax : a = x := by
        ext j; simpa using hinv j
      subst hax
      by_cases h : Disjoint a y <;> simp [reveal, Protocol.run, Disj, h]
  | cons i L ih =>
      have hi : i ∉ L := (List.nodup_cons.1 hL).1
      have hL' : L.Nodup := (List.nodup_cons.1 hL).2
      by_cases hix : i ∈ x
      · have : (reveal (i :: L) a).run x y = (reveal L (insert i a)).run x y := by
          simp [reveal, Protocol.run, hix]
        rw [this]
        refine ih hL' _ ?_
        intro j
        rcases eq_or_ne j i with rfl | hj
        · simp [hix, hi]
        · simp [Finset.mem_insert, hj, hinv j, List.mem_cons]
      · have : (reveal (i :: L) a).run x y = (reveal L a).run x y := by
          simp [reveal, Protocol.run, hix]
        rw [this]
        refine ih hL' _ ?_
        intro j
        rcases eq_or_ne j i with rfl | hj
        · simp [hix, hinv j]
        · simp [hinv j, List.mem_cons, hj]

/-- **Matching upper bound.**  There is a deterministic protocol of cost `n + 1` computing set
disjointness: Alice sends her whole set and Bob answers.  In particular the lower bounds below
are tight up to an additive constant, and the hypotheses of `CS.disjointness_lb` are
satisfiable. -/
theorem disjointness_ub (n : ℕ) :
    ∃ P : Protocol (Finset (Fin n)) (Finset (Fin n)),
      (∀ x y, P.run x y = Disj n x y) ∧ P.cost = n + 1 := by
  refine ⟨reveal (List.finRange n) ∅, ?_, ?_⟩
  · intro x y
    refine reveal_run _ (List.nodup_finRange n) _ _ _ ?_
    intro j
    simp
  · simp [reveal_cost]

/-- **Quantitative Ω(n) lower bound for randomized set disjointness (one-sided error).**

`P` is a public-coin randomized protocol: `w` is a probability distribution over the seeds `R`,
and `P r` is the deterministic protocol run on seed `r`.  It is assumed to have

* cost at most `c` for every seed,
* perfect soundness (`hsound`): it never answers "disjoint" on an intersecting pair,
* success probability at least `δ` on every disjoint pair (`hsucc`).

Then `δ * 2 ^ n ≤ 2 ^ c`: for any fixed success probability the cost is `n - O(1)`. -/
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
theorem disjointness_lb {n c : ℕ} {R : Type} [Fintype R]
    (w : R → ℝ) (hw0 : ∀ r, 0 ≤ w r) (hw1 : ∑ r, w r = 1)
    (P : R → Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hcost : ∀ r, (P r).cost ≤ c)
    (hsound : ∀ r x y, (P r).run x y = true → Disjoint x y)
    (hsucc : ∀ x y : Finset (Fin n), Disjoint x y →
      (1:ℝ)/2 ≤ ∑ r ∈ Finset.univ.filter (fun r => (P r).run x y = true), w r) :
    n ≤ c + 1 := by
  have h := disjointness_lb_of_success w hw0 hw1 P hcost hsound hsucc
  have h2 : (2:ℝ) ^ n ≤ (2:ℝ) ^ (c + 1) := by
    rw [pow_succ]
    linarith
  exact (pow_le_pow_iff_right₀ (a := (2:ℝ)) (by norm_num)).1 h2

end CS

