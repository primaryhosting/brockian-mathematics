/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`;
-- the header is repeated verbatim as a module docstring just below the imports.)

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## A model of two-party communication protocols

A deterministic protocol is a binary protocol tree.  At an `alice` node the first
player sends one bit determined by her input `x : X`; at a `bob` node the second
player sends one bit determined by his input `y : Y`; at a `leaf` the output is
produced (we allow the output at a leaf to depend on Bob's input, which makes the
model *stronger* than the usual one and hence the lower bound stronger; in
particular one-way protocols, where Bob never speaks, are covered).

The cost of a protocol is the depth of the tree, i.e. the worst-case number of
bits exchanged.
-/

/-- A deterministic two-party communication protocol. -/
inductive Prot (X Y : Type) : Type
  | leaf : (Y → Bool) → Prot X Y
  | alice : (X → Bool) → (Bool → Prot X Y) → Prot X Y
  | bob : (Y → Bool) → (Bool → Prot X Y) → Prot X Y

namespace Prot

variable {X Y : Type}

/-- The output of a protocol on a pair of inputs. -/
def run : Prot X Y → X → Y → Bool
  | .leaf g, _, y => g y
  | .alice f k, x, y => (k (f x)).run x y
  | .bob f k, x, y => (k (f y)).run x y

/-- The transcript (sequence of bits exchanged) of a protocol on a pair of inputs. -/
def tr : Prot X Y → X → Y → List Bool
  | .leaf _, _, _ => []
  | .alice f k, x, y => f x :: (k (f x)).tr x y
  | .bob f k, x, y => f y :: (k (f y)).tr x y

/-- The cost of a protocol: the depth of the protocol tree, i.e. the worst-case
number of bits exchanged. -/
def cost : Prot X Y → ℕ
  | .leaf _ => 0
  | .alice _ k => max (cost (k false)) (cost (k true)) + 1
  | .bob _ k => max (cost (k false)) (cost (k true)) + 1

/-- The finite set of all transcripts the protocol can possibly produce. -/
def trs : Prot X Y → Finset (List Bool)
  | .leaf _ => {[]}
  | .alice _ k => ((k false).trs.image (List.cons false)) ∪ ((k true).trs.image (List.cons true))
  | .bob _ k => ((k false).trs.image (List.cons false)) ∪ ((k true).trs.image (List.cons true))

theorem tr_mem_trs (P : Prot X Y) (x : X) (y : Y) : P.tr x y ∈ P.trs := by
  induction P with
  | leaf g => simp [tr, trs]
  | alice f k ih =>
      cases hfx : f x <;> simp [tr, trs, hfx] <;> exact ih _
  | bob f k ih =>
      cases hfy : f y <;> simp [tr, trs, hfy] <;> exact ih _

theorem card_trs_le (P : Prot X Y) : P.trs.card ≤ 2 ^ P.cost := by
  induction P with
  | leaf g => simp [trs, cost]
  | alice f k ih =>
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_image_of_injective _ (List.cons_injective),
          Finset.card_image_of_injective _ (List.cons_injective)]
      have h0 : (k false).trs.card ≤ 2 ^ (max (cost (k false)) (cost (k true))) :=
        le_trans (ih false) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h1 : (k true).trs.card ≤ 2 ^ (max (cost (k false)) (cost (k true))) :=
        le_trans (ih true) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (k false).trs.card + (k true).trs.card
          ≤ 2 ^ (max (cost (k false)) (cost (k true)))
            + 2 ^ (max (cost (k false)) (cost (k true))) := Nat.add_le_add h0 h1
        _ = 2 ^ (max (cost (k false)) (cost (k true)) + 1) := by rw [pow_succ]; ring
        _ = 2 ^ (Prot.alice f k).cost := rfl
  | bob f k ih =>
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_image_of_injective _ (List.cons_injective),
          Finset.card_image_of_injective _ (List.cons_injective)]
      have h0 : (k false).trs.card ≤ 2 ^ (max (cost (k false)) (cost (k true))) :=
        le_trans (ih false) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h1 : (k true).trs.card ≤ 2 ^ (max (cost (k false)) (cost (k true))) :=
        le_trans (ih true) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (k false).trs.card + (k true).trs.card
          ≤ 2 ^ (max (cost (k false)) (cost (k true)))
            + 2 ^ (max (cost (k false)) (cost (k true))) := Nat.add_le_add h0 h1
        _ = 2 ^ (max (cost (k false)) (cost (k true)) + 1) := by rw [pow_succ]; ring
        _ = 2 ^ (Prot.bob f k).cost := rfl

/-- **Rectangle property**: the set of inputs producing a given transcript is a
combinatorial rectangle, and the output only depends on the transcript and on `y`. -/
theorem rect (P : Prot X Y) : ∀ (x y x' y' : _), P.tr x y = P.tr x' y' →
    P.tr x y' = P.tr x' y' ∧ P.run x y' = P.run x' y' := by
  induction P with
  | leaf g => intro x y x' y' _; exact ⟨rfl, rfl⟩
  | alice f k ih =>
      intro x y x' y' h
      simp only [tr] at h
      obtain ⟨h1, h2⟩ := List.cons.injEq .. ▸ h
      have h2' : (k (f x)).tr x y = (k (f x)).tr x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (f x) x y x' y' h2'
      refine ⟨?_, ?_⟩
      · simp only [tr, h1]
        rw [← h1, ha, h1]
      · simp only [run, h1]
        rw [← h1, hb, h1]
  | bob f k ih =>
      intro x y x' y' h
      simp only [tr] at h
      obtain ⟨h1, h2⟩ := List.cons.injEq .. ▸ h
      have h2' : (k (f y)).tr x y = (k (f y)).tr x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (f y) x y x' y' h2'
      refine ⟨?_, ?_⟩
      · simp only [tr, ← h1]
        rw [ha]
      · simp only [run, ← h1]
        exact hb

end Prot

/-! ## Set disjointness -/

/-- The set-disjointness predicate on `n`-element ground sets: `true` iff the
sets (given by their indicator vectors) are disjoint. -/
def disj (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (∀ i, ¬ (x i = true ∧ y i = true))

theorem disj_self_compl (n : ℕ) (x : Fin n → Bool) : disj n x (fun i => !x i) = true := by
  simp [disj]

theorem eq_of_disj_compl {n : ℕ} {x x' : Fin n → Bool}
    (h : disj n x (fun i => !x' i) = true) (h' : disj n x' (fun i => !x i) = true) :
    x = x' := by
  simp only [disj, decide_eq_true_eq, Bool.not_eq_true'] at h h'
  funext i
  have hi := h i
  have hi' := h' i
  cases hx : x i <;> cases hx' : x' i <;> simp_all

/-! ## The deterministic lower bound (fooling-set argument) -/

/-- **Deterministic lower bound.** Any deterministic protocol computing set
disjointness on `n`-element ground sets must communicate at least `n` bits. -/
theorem disjointness_lb_deterministic (n : ℕ) (P : Prot (Fin n → Bool) (Fin n → Bool))
    (hP : ∀ x y, P.run x y = disj n x y) : n ≤ P.cost := by
  -- the map `x ↦ transcript of (x, xᶜ)` is injective
  have hinj : Function.Injective (fun x : Fin n → Bool => P.tr x (fun i => !x i)) := by
    intro x x' hxx'
    have h1 := (P.rect x (fun i => !x i) x' (fun i => !x' i) hxx').2
    have h2 := (P.rect x' (fun i => !x' i) x (fun i => !x i) hxx'.symm).2
    have e1 : disj n x (fun i => !x' i) = true := by
      rw [← hP, h1, hP]; exact disj_self_compl n x'
    have e2 : disj n x' (fun i => !x i) = true := by
      rw [← hP, h2, hP]; exact disj_self_compl n x
    exact eq_of_disj_compl e1 e2
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card ≤ P.trs.card := by
    refine Finset.card_le_card_of_injOn (fun x => P.tr x (fun i => !x i)) ?_ ?_
    · intro x _; exact P.tr_mem_trs _ _
    · exact Function.Injective.injOn hinj
  have h2n : (2 : ℕ) ^ n ≤ 2 ^ P.cost := by
    calc (2 : ℕ) ^ n = (Finset.univ : Finset (Fin n → Bool)).card := by
              simp [Finset.card_univ]
      _ ≤ P.trs.card := hcard
      _ ≤ 2 ^ P.cost := P.card_trs_le
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2n

/-! ## A matching upper bound (the model is not degenerate)

Alice simply sends her whole input, one bit at a time; Bob then evaluates
disjointness.  This is a protocol of cost exactly `n`, so the lower bound above
is tight and the notion of cost is the intended one.
-/

/-- The protocol in which Alice sends the bits of `x` at the indices in `l`,
starting from the partial guess `acc`, after which Bob decides disjointness. -/
def sendBits {n : ℕ} : List (Fin n) → (Fin n → Bool) → Prot (Fin n → Bool) (Fin n → Bool)
  | [], acc => .leaf (fun y => disj n acc y)
  | i :: l, acc => .alice (fun x => x i) (fun b => sendBits l (Function.update acc i b))

theorem sendBits_cost {n : ℕ} (l : List (Fin n)) (acc : Fin n → Bool) :
    (sendBits l acc).cost = l.length := by
  induction l generalizing acc with
  | nil => simp [sendBits, Prot.cost]
  | cons i l ih => simp [sendBits, Prot.cost, ih]

theorem sendBits_run {n : ℕ} (x y : Fin n → Bool) :
    ∀ (l : List (Fin n)) (acc : Fin n → Bool), (∀ j, j ∉ l → acc j = x j) →
      (sendBits l acc).run x y = disj n x y := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      have : acc = x := funext fun j => hacc j (by simp)
      simp [sendBits, Prot.run, this]
  | cons i l ih =>
      intro acc hacc
      refine (ih (Function.update acc i (x i)) ?_)
      intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
        exact hacc j (by simp [hji, hj])

/-- **Upper bound.**  There is a deterministic protocol of cost `n` computing set
disjointness on `n`-element ground sets.  Together with
`CS.disjointness_lb_deterministic` this shows the deterministic communication
complexity of set disjointness is exactly `n`. -/
theorem disjointness_ub (n : ℕ) :
    ∃ P : Prot (Fin n → Bool) (Fin n → Bool),
      P.cost = n ∧ ∀ x y, P.run x y = disj n x y := by
  classical
  refine ⟨sendBits (Finset.univ : Finset (Fin n)).toList (fun _ => false), ?_, ?_⟩
  · rw [sendBits_cost]
    simp
  · intro x y
    refine sendBits_run x y _ _ ?_
    intro j hj
    exact absurd (by simp : j ∈ (Finset.univ : Finset (Fin n)).toList) hj

/-! ## The randomized lower bound

A public-coin randomized protocol is a family of deterministic protocols indexed by
a uniformly random coin string `r : R`.  Its cost is the worst-case cost over `r`.

The result proved here is the small-error regime: if on every input the protocol
errs with probability less than `4 ^ (-n)` (in particular, for zero-error /
Las Vegas protocols), then its cost is at least `n`, i.e. `Ω(n)`.  The proof is a
union bound over the `4 ^ n` inputs, reducing to the deterministic fooling-set
bound above.

The *constant*-error version of this statement (error `1/3`, the
Kalyanasundaram–Schnitger–Razborov theorem) is a much deeper result and is **not**
formalized here; nothing below assumes it.
-/

/-- **Randomized lower bound (Ω(n)).**  Let `P` be a public-coin randomized protocol
for set disjointness on `n`-element ground sets: on each input the probability
(over the uniform coins `r : R`) that the protocol errs is less than `4⁻ⁿ`.  Then
some coin setting forces at least `n` bits of communication; equivalently the
worst-case cost of the protocol is at least `n`. -/
theorem disjointness_lb (n : ℕ) (R : Type) [Fintype R] [DecidableEq R]
    (P : R → Prot (Fin n → Bool) (Fin n → Bool)) (c : ℕ)
    (herr : ∀ x y : Fin n → Bool,
      4 ^ n * (Finset.univ.filter (fun r => (P r).run x y ≠ disj n x y)).card
        < Fintype.card R)
    (hcost : ∀ r, (P r).cost ≤ c) : n ≤ c := by
  classical
  -- the set of coin settings that err on *some* input
  set B : Finset R :=
    Finset.univ.filter (fun r => ∃ x y : Fin n → Bool, (P r).run x y ≠ disj n x y) with hB
  -- union bound
  have hsub : B ⊆ (Finset.univ : Finset ((Fin n → Bool) × (Fin n → Bool))).biUnion
      (fun p => Finset.univ.filter (fun r => (P r).run p.1 p.2 ≠ disj n p.1 p.2)) := by
    intro r hr
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨x, y, hxy⟩ := hr
    exact Finset.mem_biUnion.mpr ⟨(x, y), Finset.mem_univ _, by simpa using hxy⟩
  have hNpos : 0 < 4 ^ n := by positivity
  have hcardB : 4 ^ n * B.card ≤ 4 ^ n * (Fintype.card R - 1) := by
    calc 4 ^ n * B.card
        ≤ 4 ^ n * ∑ p : (Fin n → Bool) × (Fin n → Bool),
            (Finset.univ.filter (fun r => (P r).run p.1 p.2 ≠ disj n p.1 p.2)).card := by
          exact Nat.mul_le_mul_left _
            (le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le))
      _ = ∑ p : (Fin n → Bool) × (Fin n → Bool),
            4 ^ n * (Finset.univ.filter (fun r => (P r).run p.1 p.2 ≠ disj n p.1 p.2)).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _p : (Fin n → Bool) × (Fin n → Bool), (Fintype.card R - 1) := by
          refine Finset.sum_le_sum ?_
          intro p _
          exact Nat.le_sub_one_of_lt (herr p.1 p.2)
      _ = 4 ^ n * (Fintype.card R - 1) := by
          have hcard : Fintype.card ((Fin n → Bool) × (Fin n → Bool)) = 4 ^ n := by
            simp [Fintype.card_prod, ← mul_pow]
          rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
  have hRpos : 0 < Fintype.card R := by
    have := herr (fun _ => false) (fun _ => false)
    omega
  have hBlt : B.card < Fintype.card R := by
    have := Nat.le_of_mul_le_mul_left hcardB hNpos
    omega
  -- hence some coin setting is correct on every input
  have : ∃ r : R, r ∉ B := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset R) ⊆ B := fun r _ => hcon r
    have := Finset.card_le_card this
    simp only [Finset.card_univ] at this
    omega
  obtain ⟨r, hr⟩ := this
  have hgood : ∀ x y, (P r).run x y = disj n x y := by
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hr
    intro x y
    have := hr x
    simp only [ne_eq, not_not] at this
    exact this y
  exact le_trans (disjointness_lb_deterministic n (P r) hgood) (hcost r)

end CS

#print axioms CS.disjointness_lb
#print axioms CS.disjointness_lb_deterministic
#print axioms CS.disjointness_ub

