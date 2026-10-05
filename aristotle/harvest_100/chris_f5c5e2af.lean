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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Set disjointness has `Ω(n)` randomized communication complexity

We formalise two-party communication protocols as decision trees (`CS.Protocol`), where
`CS.Protocol.cost` is the depth of the tree, i.e. the worst-case number of bits exchanged.

A *public-coin randomized protocol* is modelled as a finite family `P : Fin m → Protocol X Y`
of deterministic protocols, run under the uniform distribution on `Fin m` (allowing repetitions
in the family, this captures every distribution with rational probabilities).

The main theorem `CS.disjointness_lb` states the `Ω(n)` lower bound for randomized protocols
with *one-sided error* (false-biased protocols): if every protocol in the family is sound
(it never accepts a pair of intersecting sets) and, for every disjoint pair, at least half of
the protocols accept, then some protocol in the family has cost at least `n - 1`.

The engine is the classical fooling-set bound `CS.Protocol.fooling_card_le`, proved by
induction on the protocol tree, together with a double counting argument over the fooling set
`{ (x, xᶜ) : x ∈ {0,1}ⁿ }` of size `2ⁿ`.
-/

namespace CS

variable {X Y : Type*}

/-- A deterministic two-party communication protocol, as a decision tree.
`nodeA g t0 t1` means Alice sends the bit `g x` and the protocol continues in `t1` (if the bit
is `true`) or `t0` (if it is `false`); `nodeB` is the same with Bob speaking. -/
inductive Protocol (X Y : Type*) : Type _
  | leaf : Bool → Protocol X Y
  | nodeA : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | nodeB : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number of
bits exchanged. -/
def cost : Protocol X Y → ℕ
  | leaf _ => 0
  | nodeA _ t0 t1 => max t0.cost t1.cost + 1
  | nodeB _ t0 t1 => max t0.cost t1.cost + 1

/-- The output of a protocol on a pair of inputs. -/
def run : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | nodeA g t0 t1, x, y => if g x then t1.run x y else t0.run x y
  | nodeB g t0 t1, x, y => if g y then t1.run x y else t0.run x y

end Protocol

/-- `IsFooling f F` says that `F` is a fooling set for the Boolean function `f`: any two
distinct pairs in `F` have a "crossed" pair on which `f` is `false`. -/
def IsFooling (f : X → Y → Bool) (F : Finset (X × Y)) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → f p.1 q.2 = false ∨ f q.1 p.2 = false

/-- **Fooling set bound.** If a protocol `P` never accepts a pair from `A × B` on which `f` is
`false`, and `F ⊆ A × B` is a fooling set for `f` all of whose elements are accepted by `P`,
then `F` has at most `2 ^ P.cost` elements. -/
theorem Protocol.fooling_card_le (f : X → Y → Bool) :
    ∀ (P : Protocol X Y) (A : Set X) (B : Set Y) (F : Finset (X × Y)),
      (∀ x ∈ A, ∀ y ∈ B, P.run x y = true → f x y = true) →
      (∀ p ∈ F, p.1 ∈ A ∧ p.2 ∈ B ∧ P.run p.1 p.2 = true) →
      IsFooling f F → F.card ≤ 2 ^ P.cost := by
  intro P
  induction P with
  | leaf b =>
      intro A B F hsound hmem hfool
      cases b with
      | false =>
          have hF : F = ∅ := by
            refine Finset.eq_empty_iff_forall_notMem.mpr ?_
            intro p hp
            have h := (hmem p hp).2.2
            simp [Protocol.run] at h
          simp [hF]
      | true =>
          have hcard : F.card ≤ 1 := by
            refine Finset.card_le_one.mpr ?_
            intro p hp q hq
            by_contra hne
            rcases hfool p hp q hq hne with h | h
            · have := hsound p.1 (hmem p hp).1 q.2 (hmem q hq).2.1 (by simp [Protocol.run])
              simp [this] at h
            · have := hsound q.1 (hmem q hq).1 p.2 (hmem p hp).2.1 (by simp [Protocol.run])
              simp [this] at h
          calc F.card ≤ 1 := hcard
            _ ≤ 2 ^ (Protocol.leaf (X := X) (Y := Y) true).cost := by
                simp [Protocol.cost]
  | nodeA g t0 t1 ih0 ih1 =>
      intro A B F hsound hmem hfool
      classical
      have hsub : ∀ (F' : Finset (X × Y)), F' ⊆ F → IsFooling f F' := by
        intro F' hF' p hp q hq hne
        exact hfool p (hF' hp) q (hF' hq) hne
      have h1 : (F.filter (fun p => g p.1 = true)).card ≤ 2 ^ t1.cost := by
        refine ih1 (A ∩ {x | g x = true}) B _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          have hgx : g x = true := hx.2
          exact hsound x hx.1 y hy (by rw [Protocol.run, if_pos hgx]; exact hrun)
        · intro p hp
          rw [Finset.mem_filter] at hp
          refine ⟨⟨(hmem p hp.1).1, hp.2⟩, (hmem p hp.1).2.1, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_pos hp.2] at this
          exact this
      have h0 : (F.filter (fun p => ¬ (g p.1 = true))).card ≤ 2 ^ t0.cost := by
        refine ih0 (A ∩ {x | g x = false}) B _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          refine hsound x hx.1 y hy ?_
          have : g x = false := hx.2
          simp [Protocol.run, this, hrun]
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hg : g p.1 = false := by simpa using hp.2
          refine ⟨⟨(hmem p hp.1).1, hg⟩, (hmem p hp.1).2.1, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_neg (by simp [hg])] at this
          exact this
      have hsplit : (F.filter (fun p => g p.1 = true)).card
          + (F.filter (fun p => ¬ (g p.1 = true))).card = F.card :=
        Finset.card_filter_add_card_filter_not _
      have hmax0 : (2 : ℕ) ^ t0.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hmax1 : (2 : ℕ) ^ t1.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : F.card ≤ 2 ^ max t0.cost t1.cost + 2 ^ max t0.cost t1.cost := by
        rw [← hsplit]
        exact Nat.add_le_add (h1.trans hmax1) (h0.trans hmax0)
      simpa [Protocol.cost, two_mul, pow_succ, mul_comm] using this
  | nodeB g t0 t1 ih0 ih1 =>
      intro A B F hsound hmem hfool
      classical
      have hsub : ∀ (F' : Finset (X × Y)), F' ⊆ F → IsFooling f F' := by
        intro F' hF' p hp q hq hne
        exact hfool p (hF' hp) q (hF' hq) hne
      have h1 : (F.filter (fun p => g p.2 = true)).card ≤ 2 ^ t1.cost := by
        refine ih1 A (B ∩ {y | g y = true}) _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          have hgy : g y = true := hy.2
          exact hsound x hx y hy.1 (by rw [Protocol.run, if_pos hgy]; exact hrun)
        · intro p hp
          rw [Finset.mem_filter] at hp
          refine ⟨(hmem p hp.1).1, ⟨(hmem p hp.1).2.1, hp.2⟩, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_pos hp.2] at this
          exact this
      have h0 : (F.filter (fun p => ¬ (g p.2 = true))).card ≤ 2 ^ t0.cost := by
        refine ih0 A (B ∩ {y | g y = false}) _ ?_ ?_ (hsub _ (Finset.filter_subset _ _))
        · intro x hx y hy hrun
          refine hsound x hx y hy.1 ?_
          have : g y = false := hy.2
          simp [Protocol.run, this, hrun]
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hg : g p.2 = false := by simpa using hp.2
          refine ⟨(hmem p hp.1).1, ⟨(hmem p hp.1).2.1, hg⟩, ?_⟩
          have := (hmem p hp.1).2.2
          rw [Protocol.run, if_neg (by simp [hg])] at this
          exact this
      have hsplit : (F.filter (fun p => g p.2 = true)).card
          + (F.filter (fun p => ¬ (g p.2 = true))).card = F.card :=
        Finset.card_filter_add_card_filter_not _
      have hmax0 : (2 : ℕ) ^ t0.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hmax1 : (2 : ℕ) ^ t1.cost ≤ 2 ^ max t0.cost t1.cost :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : F.card ≤ 2 ^ max t0.cost t1.cost + 2 ^ max t0.cost t1.cost := by
        rw [← hsplit]
        exact Nat.add_le_add (h1.trans hmax1) (h0.trans hmax0)
      simpa [Protocol.cost, two_mul, pow_succ, mul_comm] using this

/-- The set-disjointness function on subsets of `Fin n`, encoded as characteristic vectors. -/
def Disj (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (∀ i : Fin n, ¬ (x i = true ∧ y i = true))

/-- The complement of a characteristic vector. -/
def compl' {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => ! x i

theorem disj_self_compl {n : ℕ} (x : Fin n → Bool) : Disj n x (compl' x) = true := by
  simp [Disj, compl']

/-- The pairs `(x, xᶜ)` form a fooling set for disjointness. -/
theorem disj_fooling {n : ℕ} {x x' : Fin n → Bool} (h : x ≠ x') :
    Disj n x (compl' x') = false ∨ Disj n x' (compl' x) = false := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
    by_contra hc
    exact h (funext fun i => by simpa using not_exists.mp hc i)
  cases hx : x i with
  | true =>
      have hx' : x' i = false := by
        cases hx' : x' i with
        | true => rw [hx, hx'] at hi; exact absurd rfl hi
        | false => rfl
      left
      simp only [Disj, compl', decide_eq_false_iff_not, not_forall, not_not]
      exact ⟨i, by simp [hx, hx']⟩
  | false =>
      have hx' : x' i = true := by
        cases hx' : x' i with
        | true => rfl
        | false => rw [hx, hx'] at hi; exact absurd rfl hi
      right
      simp only [Disj, compl', decide_eq_false_iff_not, not_forall, not_not]
      exact ⟨i, by simp [hx, hx']⟩

/-- Any single deterministic protocol that never accepts an intersecting pair accepts at most
`2 ^ cost` of the `2 ^ n` pairs `(x, xᶜ)`. -/
theorem accepted_card_le (n : ℕ) (P : Protocol (Fin n → Bool) (Fin n → Bool))
    (hsound : ∀ x y, P.run x y = true → Disj n x y = true) :
    (Finset.univ.filter (fun x : Fin n → Bool => P.run x (compl' x) = true)).card
      ≤ 2 ^ P.cost := by
  classical
  set S := Finset.univ.filter (fun x : Fin n → Bool => P.run x (compl' x) = true) with hS
  have hinj : Function.Injective (fun x : Fin n → Bool => (x, compl' x)) := by
    intro a b hab
    exact congrArg Prod.fst hab
  have hcard : (S.image (fun x : Fin n → Bool => (x, compl' x))).card = S.card :=
    Finset.card_image_of_injective _ hinj
  rw [← hcard]
  refine Protocol.fooling_card_le (Disj n) P Set.univ Set.univ _ ?_ ?_ ?_
  · intro x _ y _ h
    exact hsound x y h
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [hS, Finset.mem_filter] at hx
    exact ⟨trivial, trivial, hx.2⟩
  · intro p hp q hq hne
    rw [Finset.mem_image] at hp hq
    obtain ⟨x, _, rfl⟩ := hp
    obtain ⟨x', _, rfl⟩ := hq
    have hxx : x ≠ x' := by
      intro h; exact hne (by rw [h])
    exact disj_fooling hxx

/-- **Set disjointness has `Ω(n)` randomized communication complexity.**

A public-coin randomized protocol is a family `P : Fin m → Protocol X Y` of deterministic
protocols, run under the uniform distribution on `Fin m`. Assume it computes set disjointness
on `{0,1}ⁿ` with one-sided error:

* `hsound`: no protocol in the family ever accepts a pair of intersecting sets;
* `hcomp`: for every disjoint pair, at least half of the protocols accept.

Then some protocol in the family has communication cost at least `n - 1`; that is, the
randomized communication complexity of disjointness is at least `n - 1 = Ω(n)`. -/
theorem disjointness_lb (n m : ℕ) (hm : 0 < m)
    (P : Fin m → Protocol (Fin n → Bool) (Fin n → Bool))
    (hsound : ∀ k x y, (P k).run x y = true → Disj n x y = true)
    (hcomp : ∀ x y, Disj n x y = true →
      m ≤ 2 * (Finset.univ.filter (fun k => (P k).run x y = true)).card) :
    ∃ k, n ≤ (P k).cost + 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every protocol in the family has cost at most `n - 2`
  have hcost : ∀ k, (P k).cost + 2 ≤ n := by
    intro k
    have := hcon k
    omega
  -- double counting
  set acc : Fin m → (Fin n → Bool) → Bool := fun k x => (P k).run x (compl' x) with hacc
  have hswap : ∑ k : Fin m, (Finset.univ.filter (fun x : Fin n → Bool => acc k x = true)).card
      = ∑ x : Fin n → Bool, (Finset.univ.filter (fun k : Fin m => acc k x = true)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- lower bound on the right-hand side
  have hlow : ∀ x : Fin n → Bool,
      m ≤ 2 * (Finset.univ.filter (fun k : Fin m => acc k x = true)).card := by
    intro x
    have := hcomp x (compl' x) (disj_self_compl x)
    simpa [hacc] using this
  have hlowsum : (2 ^ n) * m ≤ 2 * ∑ x : Fin n → Bool,
      (Finset.univ.filter (fun k : Fin m => acc k x = true)).card := by
    have hcardu : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      simp
    calc (2 ^ n) * m = ∑ _x : Fin n → Bool, m := by
            rw [Finset.sum_const, hcardu, smul_eq_mul]
      _ ≤ ∑ x : Fin n → Bool, 2 * (Finset.univ.filter (fun k : Fin m => acc k x = true)).card :=
            Finset.sum_le_sum (fun x _ => hlow x)
      _ = 2 * ∑ x : Fin n → Bool, (Finset.univ.filter (fun k : Fin m => acc k x = true)).card := by
            rw [Finset.mul_sum]
  -- upper bound on the left-hand side
  have hup : ∀ k : Fin m,
      (Finset.univ.filter (fun x : Fin n → Bool => acc k x = true)).card ≤ 2 ^ (n - 2) := by
    intro k
    refine le_trans (accepted_card_le n (P k) (hsound k)) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by have := hcost k; omega)
  have hupsum : ∑ k : Fin m, (Finset.univ.filter (fun x : Fin n → Bool => acc k x = true)).card
      ≤ m * 2 ^ (n - 2) := by
    calc ∑ k : Fin m, (Finset.univ.filter (fun x : Fin n → Bool => acc k x = true)).card
        ≤ ∑ _k : Fin m, 2 ^ (n - 2) := Finset.sum_le_sum (fun k _ => hup k)
      _ = m * 2 ^ (n - 2) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  -- combine
  have hn2 : 2 ≤ n := by
    have := hcost ⟨0, hm⟩
    omega
  have hpow : 2 ^ n = 4 * 2 ^ (n - 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    simp [pow_add, mul_comm]
  have hfinal : (2 ^ n) * m ≤ 2 * (m * 2 ^ (n - 2)) := by
    refine le_trans hlowsum ?_
    exact Nat.mul_le_mul_left 2 (le_trans (le_of_eq hswap.symm) hupsum)
  rw [hpow] at hfinal
  have hpos : 0 < 2 ^ (n - 2) := Nat.two_pow_pos _
  nlinarith [hfinal, hm, hpos]


/-! ### Non-vacuity check

The hypotheses of `disjointness_lb` are satisfiable: below is an explicit (deterministic,
hence in particular randomized) protocol computing set disjointness for `n = 2`. -/

/-- An explicit protocol computing disjointness on `Fin 2 → Bool`. -/
def exampleProtocol : Protocol (Fin 2 → Bool) (Fin 2 → Bool) :=
  let Q : Protocol (Fin 2 → Bool) (Fin 2 → Bool) :=
    Protocol.nodeA (fun x => x 1) (Protocol.leaf true)
      (Protocol.nodeB (fun y => y 1) (Protocol.leaf true) (Protocol.leaf false))
  Protocol.nodeA (fun x => x 0) Q (Protocol.nodeB (fun y => y 0) Q (Protocol.leaf false))

theorem exampleProtocol_correct (x y : Fin 2 → Bool) :
    exampleProtocol.run x y = Disj 2 x y := by
  revert x y
  decide

/-- The hypotheses of `disjointness_lb` are satisfiable (for `n = 2`, `m = 1`). -/
theorem disjointness_lb_hypotheses_satisfiable :
    ∃ P : Fin 1 → Protocol (Fin 2 → Bool) (Fin 2 → Bool),
      (∀ k x y, (P k).run x y = true → Disj 2 x y = true) ∧
      (∀ x y, Disj 2 x y = true →
        1 ≤ 2 * (Finset.univ.filter (fun k => (P k).run x y = true)).card) := by
  classical
  refine ⟨fun _ => exampleProtocol, fun k x y h => ?_, fun x y h => ?_⟩
  · rw [exampleProtocol_correct] at h; exact h
  · have hx : exampleProtocol.run x y = true := by rw [exampleProtocol_correct]; exact h
    simp [hx]

end CS

