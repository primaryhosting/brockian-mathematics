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

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/
def cost : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ p q => max p.cost q.cost + 1
  | bob _ p q => max p.cost q.cost + 1

/-- The transcript (the list of bits exchanged) on input `(x, y)`. -/
def transcript : Protocol X Y → X → Y → List Bool
  | leaf _, _, _ => []
  | alice f p q, x, y => if f x then true :: p.transcript x y else false :: q.transcript x y
  | bob f p q, x, y => if f y then true :: p.transcript x y else false :: q.transcript x y

/-- The output of the protocol on input `(x, y)`. -/
def run : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice f p q, x, y => if f x then p.run x y else q.run x y
  | bob f p q, x, y => if f y then p.run x y else q.run x y

/-- **Rectangle property.**  If `(x₁, y₁)` and `(x₂, y₂)` produce the same transcript, then so
does the "crossed" input `(x₁, y₂)`, and in particular the protocol gives the same answer there. -/
theorem rectangle : ∀ (p : Protocol X Y) (x₁ x₂ : X) (y₁ y₂ : Y),
    p.transcript x₁ y₁ = p.transcript x₂ y₂ →
      p.transcript x₁ y₂ = p.transcript x₁ y₁ ∧ p.run x₁ y₂ = p.run x₁ y₁ := by
  intro p
  induction p with
  | leaf b => intro x₁ x₂ y₁ y₂ _; exact ⟨rfl, rfl⟩
  | alice f p q ihp ihq =>
      intro x₁ x₂ y₁ y₂ h
      by_cases h1 : f x₁ = true <;> by_cases h2 : f x₂ = true <;>
        simp only [transcript, run, h1, h2, if_true, Bool.false_eq_true,
          List.cons.injEq, true_and, false_and, if_neg, not_false_iff] at h ⊢
      all_goals first
        | exact ihp x₁ x₂ y₁ y₂ h
        | exact ihq x₁ x₂ y₁ y₂ h
        | (exfalso; simp at h)
  | bob f p q ihp ihq =>
      intro x₁ x₂ y₁ y₂ h
      by_cases h1 : f y₁ = true <;> by_cases h2 : f y₂ = true <;>
        simp only [transcript, run, h1, h2, if_true, Bool.false_eq_true,
          List.cons.injEq, true_and, false_and, if_neg, not_false_iff] at h ⊢
      all_goals first
        | exact ihp x₁ x₂ y₁ y₂ h
        | exact ihq x₁ x₂ y₁ y₂ h
        | (exfalso; simp at h)

/-- A protocol of cost `c` produces at most `2 ^ c` distinct transcripts. -/
theorem card_image_transcript_le : ∀ (p : Protocol X Y) (A : Finset (X × Y)),
    (A.image fun z => p.transcript z.1 z.2).card ≤ 2 ^ p.cost := by
  intro p
  induction p with
  | leaf b =>
      intro A
      have hsub : (A.image fun z => (leaf b : Protocol X Y).transcript z.1 z.2) ⊆ {[]} := by
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨z, _, rfl⟩ := ht
        simp [transcript]
      have := Finset.card_le_card hsub
      simpa [cost] using this
  | alice f p q ihp ihq =>
      intro A
      have hsub : (A.image fun z => (alice f p q).transcript z.1 z.2) ⊆
          ((A.image fun z => p.transcript z.1 z.2).image (List.cons true)) ∪
          ((A.image fun z => q.transcript z.1 z.2).image (List.cons false)) := by
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨z, hz, rfl⟩ := ht
        by_cases hb : f z.1 = true
        · simp only [transcript, hb, if_true, Finset.mem_union, Finset.mem_image]
          exact Or.inl ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        · simp only [transcript, hb, if_false, Finset.mem_union, Finset.mem_image,
            Bool.false_eq_true]
          exact Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 : (2:ℕ) ^ p.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2:ℕ) ^ q.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hu := Finset.card_le_card hsub
      have hunion := Finset.card_union_le
        ((A.image fun z => p.transcript z.1 z.2).image (List.cons true))
        ((A.image fun z => q.transcript z.1 z.2).image (List.cons false))
      have hip : (((A.image fun z => p.transcript z.1 z.2).image (List.cons true))).card
          ≤ (A.image fun z => p.transcript z.1 z.2).card := Finset.card_image_le
      have hiq : (((A.image fun z => q.transcript z.1 z.2).image (List.cons false))).card
          ≤ (A.image fun z => q.transcript z.1 z.2).card := Finset.card_image_le
      have hp := ihp A
      have hq := ihq A
      have hcost : (alice f p q).cost = max p.cost q.cost + 1 := rfl
      rw [hcost, pow_succ]
      omega
  | bob f p q ihp ihq =>
      intro A
      have hsub : (A.image fun z => (bob f p q).transcript z.1 z.2) ⊆
          ((A.image fun z => p.transcript z.1 z.2).image (List.cons true)) ∪
          ((A.image fun z => q.transcript z.1 z.2).image (List.cons false)) := by
        intro t ht
        simp only [Finset.mem_image] at ht
        obtain ⟨z, hz, rfl⟩ := ht
        by_cases hb : f z.2 = true
        · simp only [transcript, hb, if_true, Finset.mem_union, Finset.mem_image]
          exact Or.inl ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        · simp only [transcript, hb, if_false, Finset.mem_union, Finset.mem_image,
            Bool.false_eq_true]
          exact Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have h1 : (2:ℕ) ^ p.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2:ℕ) ^ q.cost ≤ 2 ^ (max p.cost q.cost) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hu := Finset.card_le_card hsub
      have hunion := Finset.card_union_le
        ((A.image fun z => p.transcript z.1 z.2).image (List.cons true))
        ((A.image fun z => q.transcript z.1 z.2).image (List.cons false))
      have hip : (((A.image fun z => p.transcript z.1 z.2).image (List.cons true))).card
          ≤ (A.image fun z => p.transcript z.1 z.2).card := Finset.card_image_le
      have hiq : (((A.image fun z => q.transcript z.1 z.2).image (List.cons false))).card
          ≤ (A.image fun z => q.transcript z.1 z.2).card := Finset.card_image_le
      have hp := ihp A
      have hq := ihq A
      have hcost : (bob f p q).cost = max p.cost q.cost + 1 := rfl
      rw [hcost, pow_succ]
      omega

end Protocol

/-- The set-disjointness function on subsets of an `n`-element ground set. -/
def Disj (n : ℕ) (S T : Finset (Fin n)) : Bool := decide (Disjoint S T)

/-- The fooling-set property of disjointness: for `S ≠ T` at least one of the crossed pairs
`(S, Tᶜ)`, `(T, Sᶜ)` fails to be disjoint. -/
theorem fooling_cross {n : ℕ} {S T : Finset (Fin n)} (h : S ≠ T) :
    ¬ Disjoint S Tᶜ ∨ ¬ Disjoint T Sᶜ := by
  classical
  rw [Ne, Finset.ext_iff] at h
  obtain ⟨a, ha⟩ := not_forall.mp h
  by_cases haS : a ∈ S
  · have haT : a ∉ T := fun hh => ha ⟨fun _ => hh, fun _ => haS⟩
    exact Or.inl (Finset.not_disjoint_iff.mpr ⟨a, haS, by simpa using haT⟩)
  · have haT : a ∈ T := by
      by_contra hh
      exact ha ⟨fun z => absurd z haS, fun z => absurd z hh⟩
    exact Or.inr (Finset.not_disjoint_iff.mpr ⟨a, haT, by simpa using haS⟩)

/-- For a single deterministic protocol that never accepts an intersecting pair, the number of
sets `S` for which the pair `(S, Sᶜ)` is accepted is at most `2 ^ cost`. -/
theorem card_accepted_le {n : ℕ} (p : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hsound : ∀ S T : Finset (Fin n), ¬ Disjoint S T → p.run S T = false) :
    (Finset.univ.filter fun S : Finset (Fin n) => p.run S Sᶜ = true).card ≤ 2 ^ p.cost := by
  classical
  set A : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S : Finset (Fin n) => p.run S Sᶜ = true with hA
  set B : Finset (Finset (Fin n) × Finset (Fin n)) := A.image (fun S => (S, Sᶜ)) with hB
  have hcardB : B.card = A.card := by
    rw [hB]
    exact Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab)
  have hinj : Set.InjOn (fun z : Finset (Fin n) × Finset (Fin n) => p.transcript z.1 z.2)
      (B : Set (Finset (Fin n) × Finset (Fin n))) := by
    intro z₁ hz₁ z₂ hz₂ hteq
    simp only [hB, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz₁ hz₂
    obtain ⟨S, hS, rfl⟩ := hz₁
    obtain ⟨T, hT, rfl⟩ := hz₂
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hS hT
    simp only at hteq
    by_cases hST : S = T
    · subst hST; rfl
    · exfalso
      have h1 : p.run S Tᶜ = true := by
        have hr := (Protocol.rectangle p S T Sᶜ Tᶜ hteq).2
        rw [hr]; exact hS
      have h2 : p.run T Sᶜ = true := by
        have hr := (Protocol.rectangle p T S Tᶜ Sᶜ hteq.symm).2
        rw [hr]; exact hT
      rcases fooling_cross hST with hc | hc
      · rw [hsound S Tᶜ hc] at h1; exact Bool.noConfusion h1
      · rw [hsound T Sᶜ hc] at h2; exact Bool.noConfusion h2
  calc A.card = B.card := hcardB.symm
    _ = (B.image fun z => p.transcript z.1 z.2).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ 2 ^ p.cost := Protocol.card_image_transcript_le p B

/-- **Set disjointness has Ω(n) randomized communication complexity.**

A public-coin randomized protocol is a family `P : Fin m → Protocol _ _` of deterministic
protocols, run after drawing the public random string `r` uniformly from `Fin m`; its cost is
the worst-case cost `sup r, (P r).cost`.

If such a protocol computes set-disjointness on subsets of an `n`-element ground set with
one-sided error smaller than `1/2` — it never claims that two intersecting sets are disjoint
(`hsound`), and on disjoint inputs it answers correctly with probability strictly greater than
`1/2` (`hcomplete`) — then its cost is at least `n`.

Scope of the statement: the error is one-sided, i.e. the protocol has perfect soundness
(`hsound`) and is only allowed to err, with probability `< 1/2`, on disjoint pairs.  The
two-sided bounded-error version of this lower bound (Kalyanasundaram–Schnitger, Razborov) is a
strictly stronger statement and is not established here. -/
theorem disjointness_lb (n m : ℕ) (P : Fin m → Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hsound : ∀ (r : Fin m) (S T : Finset (Fin n)), ¬ Disjoint S T → (P r).run S T = false)
    (hcomplete : ∀ S T : Finset (Fin n), Disjoint S T →
      m < 2 * (Finset.univ.filter fun r : Fin m => (P r).run S T = true).card) :
    n ≤ Finset.univ.sup fun r : Fin m => (P r).cost := by
  classical
  set C : ℕ := Finset.univ.sup fun r : Fin m => (P r).cost with hC
  -- each fixed random string accepts at most `2 ^ C` of the fooling pairs
  have hrow : ∀ r : Fin m,
      (Finset.univ.filter fun S : Finset (Fin n) => (P r).run S Sᶜ = true).card ≤ 2 ^ C := by
    intro r
    refine le_trans (card_accepted_le (P r) (hsound r)) (Nat.pow_le_pow_right (by norm_num) ?_)
    exact Finset.le_sup (f := fun r : Fin m => (P r).cost) (Finset.mem_univ r)
  -- double counting
  have hswap :
      (∑ r : Fin m, (Finset.univ.filter fun S : Finset (Fin n) => (P r).run S Sᶜ = true).card)
      = ∑ S : Finset (Fin n), (Finset.univ.filter fun r : Fin m => (P r).run S Sᶜ = true).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : ∀ S : Finset (Fin n),
      m < 2 * (Finset.univ.filter fun r : Fin m => (P r).run S Sᶜ = true).card :=
    fun S => hcomplete S Sᶜ disjoint_compl_right
  have hcard : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by simp
  have h1 : (2 ^ n) * m <
      2 * ∑ S : Finset (Fin n), (Finset.univ.filter fun r : Fin m =>
        (P r).run S Sᶜ = true).card := by
    calc (2 ^ n) * m = ∑ _S : Finset (Fin n), m := by
          rw [Finset.sum_const, hcard, smul_eq_mul]
      _ < 2 * ∑ S : Finset (Fin n), (Finset.univ.filter fun r : Fin m =>
            (P r).run S Sᶜ = true).card := by
          rw [Finset.mul_sum]
          refine Finset.sum_lt_sum_of_nonempty ?_ (fun S _ => hlow S)
          exact Finset.univ_nonempty (α := Finset (Fin n))
  have h2 : (∑ S : Finset (Fin n), (Finset.univ.filter fun r : Fin m =>
      (P r).run S Sᶜ = true).card) ≤ m * 2 ^ C := by
    rw [← hswap]
    calc (∑ r : Fin m, (Finset.univ.filter fun S : Finset (Fin n) =>
            (P r).run S Sᶜ = true).card)
        ≤ ∑ _r : Fin m, 2 ^ C := Finset.sum_le_sum (fun r _ => hrow r)
      _ = m * 2 ^ C := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have key : (2 ^ n) * m < 2 * (m * 2 ^ C) := lt_of_lt_of_le h1 (by omega)
  have hlt : (2 ^ n) * m < (2 ^ (C + 1)) * m := by
    calc (2 ^ n) * m < 2 * (m * 2 ^ C) := key
      _ = (2 ^ (C + 1)) * m := by ring
  have hpow : (2:ℕ) ^ n < 2 ^ (C + 1) := lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hpow
  omega

/-- The deterministic special case: any deterministic protocol computing set disjointness on an
`n`-element ground set must communicate at least `n` bits. -/
theorem disjointness_deterministic_lb (n : ℕ) (p : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hp : ∀ S T : Finset (Fin n), p.run S T = Disj n S T) : n ≤ p.cost := by
  classical
  have h := disjointness_lb n 1 (fun _ => p) ?_ ?_
  · simpa using h
  · intro _ S T hST
    rw [hp]
    simp [Disj, hST]
  · intro S T hST
    have hfil : (Finset.univ.filter fun _ : Fin 1 => p.run S T = true) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro r _
      rw [hp]
      simp [Disj, hST]
    rw [hfil]
    simp

/-! ### A matching protocol: the lower bound is not vacuous -/

namespace Protocol

/-- The naive protocol for disjointness: Alice announces, one bit per element of the list `l`,
which elements of `l` lie in her set, and Bob then answers with one bit.  `acc` accumulates the
part of Alice's set already announced. -/
def build {n : ℕ} : List (Fin n) → Finset (Fin n) →
    Protocol (Finset (Fin n)) (Finset (Fin n))
  | [], acc => bob (fun T => Disj n acc T) (leaf true) (leaf false)
  | a :: l, acc => alice (fun S => decide (a ∈ S)) (build l (insert a acc)) (build l acc)

theorem cost_build {n : ℕ} : ∀ (l : List (Fin n)) (acc : Finset (Fin n)),
    (build l acc).cost = l.length + 1 := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih => intro acc; simp [build, cost, ih]

theorem run_build {n : ℕ} : ∀ (l : List (Fin n)) (acc S T : Finset (Fin n)),
    (build l acc).run S T = Disj n (acc ∪ S.filter (fun x => x ∈ l)) T := by
  intro l
  induction l with
  | nil =>
      intro acc S T
      simp only [build, run]
      have hemp : S.filter (fun x => x ∈ ([] : List (Fin n))) = ∅ := by simp
      rw [hemp, Finset.union_empty]
      by_cases h : Disj n acc T = true
      · rw [if_pos h, h]
      · simp only [Bool.not_eq_true] at h
        rw [h]
        simp
  | cons a l ih =>
      intro acc S T
      simp only [build, run]
      by_cases ha : a ∈ S
      · have hset : insert a acc ∪ S.filter (fun x => x ∈ l)
            = acc ∪ S.filter (fun x => x ∈ a :: l) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, List.mem_cons]
          aesop
        rw [if_pos (by simp [ha] : decide (a ∈ S) = true), ih, hset]
      · have hset : acc ∪ S.filter (fun x => x ∈ l)
            = acc ∪ S.filter (fun x => x ∈ a :: l) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, List.mem_cons]
          aesop
        rw [if_neg (by simp [ha] : ¬ (decide (a ∈ S) = true)), ih, hset]

end Protocol

/-- **Matching upper bound.**  There is a deterministic protocol of cost `n + 1` computing
set disjointness on subsets of an `n`-element ground set; in particular the hypotheses of
`CS.disjointness_lb` are satisfiable and the `Ω(n)` bound is tight up to one bit. -/
theorem disjointness_ub (n : ℕ) :
    ∃ p : Protocol (Finset (Fin n)) (Finset (Fin n)),
      (∀ S T : Finset (Fin n), p.run S T = Disj n S T) ∧ p.cost = n + 1 := by
  refine ⟨Protocol.build (List.finRange n) ∅, ?_, ?_⟩
  · intro S T
    rw [Protocol.run_build]
    have : S.filter (fun x => x ∈ List.finRange n) = S := by
      apply Finset.filter_true_of_mem
      intro x _
      simp
    rw [this, Finset.empty_union]
  · rw [Protocol.cost_build, List.length_finRange]

end CS

