/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-! ## The communication model

A two-party deterministic communication protocol on inputs `X` (Alice) and `Y` (Bob) is a
binary tree.  At an `alice` node the bit sent depends only on Alice's input, at a `bob` node
only on Bob's input, and a `leaf` carries the output of the protocol.  The `cost` of a protocol
is the depth of the tree, i.e. the number of bits exchanged in the worst case. -/
inductive Protocol (X Y : Type) : Type
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of a protocol on a given pair of inputs. -/
def run : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice f p q, x, y => if f x then q.run x y else p.run x y
  | bob g p q, x, y => if g y then q.run x y else p.run x y

/-- The communication cost (worst-case number of bits exchanged) of a protocol. -/
def cost : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ p q => max p.cost q.cost + 1
  | bob _ p q => max p.cost q.cost + 1

@[simp] lemma run_leaf (b : Bool) (x : X) (y : Y) : (leaf b : Protocol X Y).run x y = b := rfl

@[simp] lemma run_alice (f : X → Bool) (p q : Protocol X Y) (x : X) (y : Y) :
    (alice f p q).run x y = if f x then q.run x y else p.run x y := rfl

@[simp] lemma run_bob (g : Y → Bool) (p q : Protocol X Y) (x : X) (y : Y) :
    (bob g p q).run x y = if g y then q.run x y else p.run x y := rfl

@[simp] lemma cost_leaf (b : Bool) : (leaf b : Protocol X Y).cost = 0 := rfl

@[simp] lemma cost_alice (f : X → Bool) (p q : Protocol X Y) :
    (alice f p q).cost = max p.cost q.cost + 1 := rfl

@[simp] lemma cost_bob (g : Y → Bool) (p q : Protocol X Y) :
    (bob g p q).cost = max p.cost q.cost + 1 := rfl

end Protocol

/-- Inputs to the set-disjointness problem on a universe of size `n`. -/
abbrev Inp (n : ℕ) := Finset (Fin n)

/-- Set disjointness: `Disj x y = true` iff the sets `x` and `y` are disjoint. -/
def Disj {n : ℕ} (x y : Inp n) : Bool := decide (Disjoint x y)

/-! ## The fooling set

The pairs `(S, Sᶜ)`, for `S ⊆ [n]`, form a fooling set of size `2 ^ n` for disjointness:
they are all disjoint pairs, but for `S ≠ T` at least one of `(S, Tᶜ)`, `(T, Sᶜ)` is
non-disjoint.  Consequently a combinatorial rectangle all of whose pairs are disjoint
contains at most one of them. -/

lemma disjoint_compl_iff_subset {n : ℕ} (s t : Inp n) : Disjoint s tᶜ ↔ s ⊆ t := by
  simp only [Finset.disjoint_right, Finset.mem_compl]
  constructor
  · intro h x hx
    by_contra hc
    exact h hc hx
  · intro h x hx hxs
    exact hx (h hxs)

/-- Key counting lemma: if a protocol `P` accepts only disjoint pairs inside the rectangle
`A × B`, then the number of fooling-set elements `(S, Sᶜ)` with `S ∈ A`, `Sᶜ ∈ B` that it
accepts is at most `2 ^ cost P` (the number of leaves of the protocol tree). -/
lemma fooling_card_le {n : ℕ} (P : Protocol (Inp n) (Inp n)) :
    ∀ A B : Finset (Inp n),
      (∀ x ∈ A, ∀ y ∈ B, P.run x y = true → Disjoint x y) →
      (A.filter (fun S => Sᶜ ∈ B ∧ P.run S Sᶜ = true)).card ≤ 2 ^ P.cost := by
  induction P with
  | leaf b =>
      intro A B hAB
      cases b with
      | false =>
          have : A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.leaf false :
              Protocol (Inp n) (Inp n)).run S Sᶜ = true) = ∅ := by
            apply Finset.filter_false_of_mem
            intro S _
            simp
          rw [this]
          simp
      | true =>
          have hone : ∀ S ∈ A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.leaf true :
              Protocol (Inp n) (Inp n)).run S Sᶜ = true),
              ∀ T ∈ A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.leaf true :
              Protocol (Inp n) (Inp n)).run S Sᶜ = true), S = T := by
            intro S hS T hT
            simp only [Finset.mem_filter] at hS hT
            have h1 : Disjoint S Tᶜ := hAB S hS.1 Tᶜ hT.2.1 rfl
            have h2 : Disjoint T Sᶜ := hAB T hT.1 Sᶜ hS.2.1 rfl
            have := (disjoint_compl_iff_subset S T).mp h1
            have := (disjoint_compl_iff_subset T S).mp h2
            exact Finset.Subset.antisymm ‹S ⊆ T› ‹T ⊆ S›
          have := Finset.card_le_one.mpr hone
          simpa using this
  | alice f p q ihp ihq =>
      intro A B hAB
      set A0 := A.filter (fun S => f S = false) with hA0
      set A1 := A.filter (fun S => f S = true) with hA1
      have hp : (A0.filter (fun S => Sᶜ ∈ B ∧ p.run S Sᶜ = true)).card ≤ 2 ^ p.cost := by
        refine ihp A0 B ?_
        intro x hx y hy hrun
        simp only [hA0, Finset.mem_filter] at hx
        refine hAB x hx.1 y hy ?_
        simp [hx.2, hrun]
      have hq : (A1.filter (fun S => Sᶜ ∈ B ∧ q.run S Sᶜ = true)).card ≤ 2 ^ q.cost := by
        refine ihq A1 B ?_
        intro x hx y hy hrun
        simp only [hA1, Finset.mem_filter] at hx
        refine hAB x hx.1 y hy ?_
        simp [hx.2, hrun]
      have hsplit :
          (A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.alice f p q).run S Sᶜ = true)).card
            = (A0.filter (fun S => Sᶜ ∈ B ∧ p.run S Sᶜ = true)).card
              + (A1.filter (fun S => Sᶜ ∈ B ∧ q.run S Sᶜ = true)).card := by
        rw [hA0, hA1, Finset.filter_filter, Finset.filter_filter]
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext S
          by_cases hf : f S = true <;>
            simp [Finset.mem_filter, Finset.mem_union, hf, Protocol.run]
        · rw [Finset.disjoint_left]
          intro S hS hS'
          simp only [Finset.mem_filter] at hS hS'
          rw [hS.2.1] at hS'
          exact Bool.false_ne_true hS'.2.1
      rw [hsplit]
      calc (A0.filter (fun S => Sᶜ ∈ B ∧ p.run S Sᶜ = true)).card
              + (A1.filter (fun S => Sᶜ ∈ B ∧ q.run S Sᶜ = true)).card
          ≤ 2 ^ p.cost + 2 ^ q.cost := Nat.add_le_add hp hq
        _ ≤ 2 ^ (max p.cost q.cost) + 2 ^ (max p.cost q.cost) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ (Protocol.alice f p q).cost := by
            rw [Protocol.cost, pow_succ]; ring
  | bob g p q ihp ihq =>
      intro A B hAB
      set B0 := B.filter (fun T => g T = false) with hB0
      set B1 := B.filter (fun T => g T = true) with hB1
      have hp : (A.filter (fun S => Sᶜ ∈ B0 ∧ p.run S Sᶜ = true)).card ≤ 2 ^ p.cost := by
        refine ihp A B0 ?_
        intro x hx y hy hrun
        simp only [hB0, Finset.mem_filter] at hy
        refine hAB x hx y hy.1 ?_
        simp [hy.2, hrun]
      have hq : (A.filter (fun S => Sᶜ ∈ B1 ∧ q.run S Sᶜ = true)).card ≤ 2 ^ q.cost := by
        refine ihq A B1 ?_
        intro x hx y hy hrun
        simp only [hB1, Finset.mem_filter] at hy
        refine hAB x hx y hy.1 ?_
        simp [hy.2, hrun]
      have hsplit :
          (A.filter (fun S => Sᶜ ∈ B ∧ (Protocol.bob g p q).run S Sᶜ = true)).card
            = (A.filter (fun S => Sᶜ ∈ B0 ∧ p.run S Sᶜ = true)).card
              + (A.filter (fun S => Sᶜ ∈ B1 ∧ q.run S Sᶜ = true)).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext S
          by_cases hg : g Sᶜ = true <;>
            simp [hB0, hB1, Finset.mem_filter, Finset.mem_union, hg, Protocol.run]
        · rw [Finset.disjoint_left]
          intro S hS hS'
          simp only [hB0, hB1, Finset.mem_filter] at hS hS'
          rw [hS.2.1.2] at hS'
          exact Bool.false_ne_true hS'.2.1.2
      rw [hsplit]
      calc (A.filter (fun S => Sᶜ ∈ B0 ∧ p.run S Sᶜ = true)).card
              + (A.filter (fun S => Sᶜ ∈ B1 ∧ q.run S Sᶜ = true)).card
          ≤ 2 ^ p.cost + 2 ^ q.cost := Nat.add_le_add hp hq
        _ ≤ 2 ^ (max p.cost q.cost) + 2 ^ (max p.cost q.cost) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ (Protocol.bob g p q).cost := by
            rw [Protocol.cost, pow_succ]; ring

/-- Specialisation of `fooling_card_le` to the full rectangle: a protocol that accepts only
disjoint pairs accepts at most `2 ^ cost` of the `2 ^ n` fooling-set pairs `(S, Sᶜ)`. -/
lemma accepted_fooling_card_le {n : ℕ} (P : Protocol (Inp n) (Inp n))
    (hsound : ∀ x y : Inp n, P.run x y = true → Disjoint x y) :
    (Finset.univ.filter (fun S : Inp n => P.run S Sᶜ = true)).card ≤ 2 ^ P.cost := by
  have h := fooling_card_le P Finset.univ Finset.univ (fun x _ y _ h => hsound x y h)
  simpa using h

/-! ## The randomized lower bound

A *public-coin randomized protocol* is a family `P : R → Protocol X Y` of deterministic
protocols indexed by a finite nonempty set `R` of random strings, drawn uniformly.

We prove an `Ω(n)` lower bound for randomized protocols with *one-sided* error: the protocol
never accepts a non-disjoint pair, and accepts a disjoint pair with probability at least
`1 / 2`.  (Two-sided error, i.e. Razborov's theorem, is not covered by this argument; indeed
the fooling-set method used here is genuinely unavailable for two-sided error.) -/

/-- General form of the lower bound, with an arbitrary success probability `1 / m`:
if a public-coin randomized protocol never accepts a non-disjoint pair and accepts every
disjoint pair with probability at least `1 / m`, and every protocol of the family costs at
most `c`, then `2 ^ n ≤ m * 2 ^ c`. -/
theorem disjointness_lb_error (n : ℕ) {R : Type} [Fintype R] [Nonempty R]
    (P : R → Protocol (Inp n) (Inp n)) (c m : ℕ)
    (hcost : ∀ r, (P r).cost ≤ c)
    (hsound : ∀ (r : R) (x y : Inp n), (P r).run x y = true → Disjoint x y)
    (hcomp : ∀ x y : Inp n, Disjoint x y →
      Fintype.card R ≤ m * (Finset.univ.filter (fun r => (P r).run x y = true)).card) :
    2 ^ n ≤ m * 2 ^ c := by
  classical
  -- For each fixed random string, the number of accepted fooling pairs is at most `2 ^ c`.
  have hper : ∀ r : R,
      (Finset.univ.filter (fun S : Inp n => (P r).run S Sᶜ = true)).card ≤ 2 ^ c := fun r =>
    le_trans (accepted_fooling_card_le (P r) (hsound r)) (Nat.pow_le_pow_right (by norm_num)
      (hcost r))
  -- Double counting of the accepted (fooling pair, random string) incidences.
  have hswap :
      (∑ r : R, (Finset.univ.filter (fun S : Inp n => (P r).run S Sᶜ = true)).card)
        = ∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : (Finset.univ : Finset (Inp n)).card * Fintype.card R
      ≤ m * ∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones (Finset.univ : Finset (Inp n)), Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro S _
    simpa using hcomp S Sᶜ disjoint_compl_right
  have hhigh :
      (∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card)
        ≤ Fintype.card R * 2 ^ c := by
    rw [← hswap]
    calc (∑ r : R, (Finset.univ.filter (fun S : Inp n => (P r).run S Sᶜ = true)).card)
        ≤ ∑ _r : R, 2 ^ c := Finset.sum_le_sum (fun r _ => hper r)
      _ = Fintype.card R * 2 ^ c := by simp [Finset.sum_const, Finset.card_univ]
  have hcard : (Finset.univ : Finset (Inp n)).card = 2 ^ n := by simp
  have hR : 0 < Fintype.card R := Fintype.card_pos
  have hmain : 2 ^ n * Fintype.card R ≤ (m * 2 ^ c) * Fintype.card R := by
    calc 2 ^ n * Fintype.card R = (Finset.univ : Finset (Inp n)).card * Fintype.card R := by
          rw [hcard]
      _ ≤ m * ∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card := hlow
      _ ≤ m * (Fintype.card R * 2 ^ c) := Nat.mul_le_mul_left m hhigh
      _ = (m * 2 ^ c) * Fintype.card R := by ring
  exact Nat.le_of_mul_le_mul_right hmain hR

/-- Main lower bound.  Any public-coin randomized protocol for set disjointness on a universe
of size `n` with one-sided error at most `1/2` — it never accepts a non-disjoint pair, and it
accepts every disjoint pair with probability at least `1/2` — must communicate at least
`n - 1` bits: if every protocol in the family costs at most `c`, then `n ≤ c + 1`. -/
theorem disjointness_lb (n : ℕ) {R : Type} [Fintype R] [Nonempty R]
    (P : R → Protocol (Inp n) (Inp n)) (c : ℕ)
    (hcost : ∀ r, (P r).cost ≤ c)
    (hsound : ∀ (r : R) (x y : Inp n), (P r).run x y = true → Disjoint x y)
    (hcomp : ∀ x y : Inp n, Disjoint x y →
      Fintype.card R ≤ 2 * (Finset.univ.filter (fun r => (P r).run x y = true)).card) :
    n ≤ c + 1 := by
  have h := disjointness_lb_error n P c 2 hcost hsound hcomp
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ (c + 1) := by
    calc (2 : ℕ) ^ n ≤ 2 * 2 ^ c := h
      _ = 2 ^ (c + 1) := by ring
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- Deterministic corollary: a deterministic protocol computing set disjointness exactly on a
universe of size `n` must communicate at least `n - 1` bits. -/
theorem disjointness_lb_deterministic (n : ℕ) (P : Protocol (Inp n) (Inp n)) (c : ℕ)
    (hcost : P.cost ≤ c) (hcorrect : ∀ x y : Inp n, P.run x y = Disj x y) :
    n ≤ c + 1 := by
  classical
  refine disjointness_lb n (R := Unit) (fun _ => P) c (fun _ => hcost) ?_ ?_
  · intro _ x y h
    rw [hcorrect] at h
    simpa [Disj] using h
  · intro x y hxy
    have hrun : P.run x y = true := by
      rw [hcorrect]
      simpa [Disj] using hxy
    simp [hrun]

/-! ## Non-vacuity: a matching upper bound

The lower bound is close to optimal, and in particular the hypotheses of `disjointness_lb`
are satisfiable: Alice can simply send her whole set (`n` bits) and Bob then announces the
answer (`1` bit), giving a deterministic — hence zero-error randomized — protocol of cost
`n + 1`. -/

/-- The set of elements of `Fin n` whose value is `k` (a singleton if `k < n`, else empty). -/
def pt (n k : ℕ) : Inp n := Finset.univ.filter (fun i : Fin n => (i : ℕ) = k)

lemma filter_eq_pt_inter {n : ℕ} (x : Inp n) (k : ℕ) :
    x.filter (fun i : Fin n => (i : ℕ) = k) = pt n k ∩ x := by
  ext i
  simp [pt, Finset.mem_inter, and_comm]

lemma pt_subset_iff {n : ℕ} (x : Inp n) (k : ℕ) :
    pt n k ⊆ x ↔ x.filter (fun i : Fin n => (i : ℕ) = k) = pt n k := by
  rw [filter_eq_pt_inter]
  constructor
  · intro h
    exact Finset.inter_eq_left.mpr h
  · intro h
    rw [← h]
    exact Finset.inter_subset_right

/-- The protocol in which Alice reveals the membership of the first `k` elements of her set
(one bit each, starting from index `k - 1`), after which Bob announces the answer. -/
def reveal (n : ℕ) : ℕ → Inp n → Protocol (Inp n) (Inp n)
  | 0, acc =>
      Protocol.bob (fun y => decide (Disjoint acc y)) (Protocol.leaf false) (Protocol.leaf true)
  | (k + 1), acc =>
      Protocol.alice (fun x => decide (pt n k ⊆ x)) (reveal n k acc) (reveal n k (acc ∪ pt n k))

lemma reveal_cost (n : ℕ) : ∀ (k : ℕ) (acc : Inp n), (reveal n k acc).cost = k + 1 := by
  intro k
  induction k with
  | zero => intro acc; rfl
  | succ k ih => intro acc; simp [reveal, ih]

lemma reveal_run (n : ℕ) : ∀ (k : ℕ) (acc x y : Inp n),
    (reveal n k acc).run x y = decide (Disjoint (acc ∪ x.filter (fun i : Fin n => (i : ℕ) < k)) y) := by
  intro k
  induction k with
  | zero =>
      intro acc x y
      simp [reveal, Protocol.run]
  | succ k ih =>
      intro acc x y
      have hsplit : x.filter (fun i : Fin n => (i : ℕ) < k + 1)
          = x.filter (fun i : Fin n => (i : ℕ) < k) ∪ x.filter (fun i : Fin n => (i : ℕ) = k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hi, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr ⟨hi, h⟩
        · rintro (⟨hi, h⟩ | ⟨hi, h⟩)
          · exact ⟨hi, Nat.lt_succ_of_lt h⟩
          · exact ⟨hi, by omega⟩
      by_cases hmem : pt n k ⊆ x
      · have hpt : x.filter (fun i : Fin n => (i : ℕ) = k) = pt n k := (pt_subset_iff x k).mp hmem
        simp only [reveal, Protocol.run, hmem, decide_true, if_true, ih]
        rw [hsplit, hpt]
        congr 2
        ext i
        simp [Finset.mem_union]
        tauto
      · have hpt : x.filter (fun i : Fin n => (i : ℕ) = k) = ∅ := by
          by_contra hne
          apply hmem
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          simp only [Finset.mem_filter] at hi
          intro j hj
          simp only [pt, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have : j = i := Fin.ext (by rw [hj, hi.2])
          rw [this]
          exact hi.1
        simp only [reveal, Protocol.run, hmem, decide_false, ih]
        rw [hsplit, hpt]
        simp

/-- Non-vacuity / near-tightness: there is a deterministic protocol of cost `n + 1` computing
set disjointness on a universe of size `n`. -/
theorem disjointness_ub (n : ℕ) :
    ∃ P : Protocol (Inp n) (Inp n), P.cost = n + 1 ∧ ∀ x y : Inp n, P.run x y = Disj x y := by
  refine ⟨reveal n n ∅, reveal_cost n n ∅, ?_⟩
  intro x y
  rw [reveal_run]
  have hx : x.filter (fun i : Fin n => (i : ℕ) < n) = x := by
    apply Finset.filter_true_of_mem
    intro i _
    exact i.isLt
  rw [hx]
  simp [Disj]

end CS

