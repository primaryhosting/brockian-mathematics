import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Barrington's theorem: the Boolean functions computed by fan-in-two Boolean circuits of
depth `d` are exactly the ones computed by width-5 permutation branching programs of
length `4 ^ d` (up to a constant factor in the exponent / a logarithm in the length).

We formalise the two quantitative directions:

* `CS.exists_bprog`  : a circuit of depth `d` is simulated by a width-5 permutation
  branching program of length at most `4 ^ d`  (the hard direction of Barrington's theorem);
* `CS.exists_circuit`: a width-5 permutation branching program of length `L` is simulated
  by a circuit of depth at most `4 * ⌈log₂ L⌉ + 6` (the easy direction).

Together (`CS.barrington`) these say `NC¹ = width-5 permutation branching programs`:
logarithmic depth corresponds to polynomial length.
-/

namespace CS

open Equiv

/-! ## Boolean circuits -/

/-- Boolean circuits with fan-in two `∧`/`∨` gates and `¬` gates, over the variables
`x 0, x 1, …`. -/
inductive Circuit where
  | const : Bool → Circuit
  | var : ℕ → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit
  deriving Inhabited

/-- The Boolean function computed by a circuit. -/
def Circuit.eval : Circuit → (ℕ → Bool) → Bool
  | const b, _ => b
  | var i, x => x i
  | not c, x => !c.eval x
  | and a b, x => a.eval x && b.eval x
  | or a b, x => a.eval x || b.eval x

/-- The depth of a circuit (the length of the longest path from an input to the output). -/
def Circuit.depth : Circuit → ℕ
  | const _ => 0
  | var _ => 0
  | not c => c.depth + 1
  | and a b => max a.depth b.depth + 1
  | or a b => max a.depth b.depth + 1

/-! ## Width-5 permutation branching programs -/

/-- One instruction of a width-5 permutation branching program: read the variable `x i`
and apply the first permutation if it is `true`, the second one if it is `false`. -/
abbrev Instr := ℕ × Perm (Fin 5) × Perm (Fin 5)

/-- A width-5 permutation branching program is a list of instructions. -/
abbrev BProg := List Instr

/-- The permutation performed by a single instruction on a given input. -/
def Instr.run (x : ℕ → Bool) (t : Instr) : Perm (Fin 5) :=
  if x t.1 then t.2.1 else t.2.2

/-- The permutation computed by a branching program: the ordered product of the
permutations performed by its instructions. -/
def BProg.eval (P : BProg) (x : ℕ → Bool) : Perm (Fin 5) := (P.map (Instr.run x)).prod

/-- `P` computes the Boolean function `f` with respect to the permutation `γ`: it outputs
`γ` on the inputs where `f` is true, and the identity elsewhere. -/
def Computes (P : BProg) (γ : Perm (Fin 5)) (f : (ℕ → Bool) → Bool) : Prop :=
  ∀ x, P.eval x = if f x then γ else 1

/-! ## Five-cycles in `S₅` -/

/-- A fixed five-cycle. -/
def g5 : Perm (Fin 5) := ([0, 1, 2, 3, 4] : List (Fin 5)).formPerm

/-- `Conj5 γ` says that `γ` is conjugate to the five-cycle `g5`, i.e. that `γ` is a
five-cycle (see `CS.conj5_iff`). -/
def Conj5 (γ : Perm (Fin 5)) : Prop := ∃ θ : Perm (Fin 5), θ * g5 * θ⁻¹ = γ

theorem conj5_g5 : Conj5 g5 := ⟨1, by group⟩

instance : DecidablePred Conj5 :=
  fun γ => inferInstanceAs (Decidable (∃ θ : Perm (Fin 5), θ * g5 * θ⁻¹ = γ))

set_option maxRecDepth 100000 in
/-- `Conj5` really is the set of five-cycles: the nonidentity elements of order dividing
(hence equal to) `5`. -/
theorem conj5_iff (γ : Perm (Fin 5)) : Conj5 γ ↔ (γ ^ 5 = 1 ∧ γ ≠ 1) := by
  revert γ; decide

/-- An element conjugating `g5` to its inverse. -/
private def pinv : Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 2 3

/-- Two five-cycles whose commutator is `g5`. -/
private def s0 : Perm (Fin 5) := ([0, 3, 2, 4, 1] : List (Fin 5)).formPerm
private def t0 : Perm (Fin 5) := ([0, 3, 1, 2, 4] : List (Fin 5)).formPerm
/-- Elements conjugating `g5` to `s0`, resp. `t0`. -/
private def a0 : Perm (Fin 5) := ([0, 3, 1, 2, 4] : List (Fin 5)).formPerm
private def b0 : Perm (Fin 5) := ([0, 4, 2, 3, 1] : List (Fin 5)).formPerm

private theorem hpinv : pinv * g5 * pinv⁻¹ = g5⁻¹ := by decide
private theorem hs0 : a0 * g5 * a0⁻¹ = s0 := by decide
private theorem ht0 : b0 * g5 * b0⁻¹ = t0 := by decide
private theorem hcomm : s0 * t0 * s0⁻¹ * t0⁻¹ = g5 := by decide

theorem Conj5.inv {γ : Perm (Fin 5)} (h : Conj5 γ) : Conj5 γ⁻¹ := by
  obtain ⟨θ, rfl⟩ := h
  refine ⟨θ * pinv, ?_⟩
  have h' : (θ * g5 * θ⁻¹)⁻¹ = θ * g5⁻¹ * θ⁻¹ := by group
  rw [h', ← hpinv]; group

/-- Every five-cycle is a commutator of two five-cycles. -/
theorem Conj5.commutator {γ : Perm (Fin 5)} (h : Conj5 γ) :
    ∃ σ τ : Perm (Fin 5), Conj5 σ ∧ Conj5 τ ∧ σ * τ * σ⁻¹ * τ⁻¹ = γ := by
  obtain ⟨θ, rfl⟩ := h
  refine ⟨θ * s0 * θ⁻¹, θ * t0 * θ⁻¹, ⟨θ * a0, ?_⟩, ⟨θ * b0, ?_⟩, ?_⟩
  · rw [← hs0]; group
  · rw [← ht0]; group
  · rw [← hcomm]; group

/-! ## Operations on branching programs -/

/-- The reversed program with all permutations inverted; it computes the inverse. -/
def BProg.inv (P : BProg) : BProg := (P.map fun t => (t.1, t.2.1⁻¹, t.2.2⁻¹)).reverse

/-- Multiply the output of a (nonempty) program on the left by a constant `g`, by
modifying its first instruction. -/
def BProg.pre (g : Perm (Fin 5)) : BProg → BProg
  | [] => []
  | t :: r => (t.1, g * t.2.1, g * t.2.2) :: r

theorem BProg.eval_append (P Q : BProg) (x : ℕ → Bool) :
    (P ++ Q).eval x = P.eval x * Q.eval x := by
  simp [BProg.eval]

theorem BProg.eval_inv (P : BProg) (x : ℕ → Bool) : P.inv.eval x = (P.eval x)⁻¹ := by
  rw [BProg.eval, BProg.eval, List.prod_inv_reverse, BProg.inv]
  congr 1
  simp only [List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, Instr.run]
  split <;> rfl

theorem BProg.length_inv (P : BProg) : P.inv.length = P.length := by simp [BProg.inv]

theorem BProg.eval_pre (g : Perm (Fin 5)) (P : BProg) (hP : P ≠ []) (x : ℕ → Bool) :
    (P.pre g).eval x = g * P.eval x := by
  cases P with
  | nil => exact absurd rfl hP
  | cons t r =>
      simp only [BProg.pre, BProg.eval, List.map_cons, List.prod_cons, ← mul_assoc]
      congr 1
      simp only [Instr.run]
      split <;> rfl

theorem BProg.length_pre (g : Perm (Fin 5)) (P : BProg) : (P.pre g).length = P.length := by
  cases P <;> simp [BProg.pre]

theorem BProg.pre_ne_nil (g : Perm (Fin 5)) {P : BProg} (hP : P ≠ []) : P.pre g ≠ [] := by
  cases P with
  | nil => exact absurd rfl hP
  | cons t r => simp [BProg.pre]

/-! ## The hard direction of Barrington's theorem -/

/-- Negation is free: prepending the constant `γ` to a program computing `f` with respect
to `γ⁻¹` yields a program computing `¬f` with respect to `γ`. -/
theorem neg_computes {P : BProg} (hP : P ≠ []) {γ : Perm (Fin 5)} {f : (ℕ → Bool) → Bool}
    (h : Computes P γ⁻¹ f) : Computes (P.pre γ) γ (fun x => !f x) := by
  intro x
  rw [BProg.eval_pre _ _ hP, h x]
  rcases Bool.eq_false_or_eq_true (f x) with hf | hf <;> simp only [hf] <;> simp

/-- The commutator trick: concatenating `P`, `Q` and their inverses computes the
conjunction with respect to the commutator of the two permutations. -/
theorem and_computes {P Q : BProg} {σ τ : Perm (Fin 5)} {f g : (ℕ → Bool) → Bool}
    (h1 : Computes P σ f) (h2 : Computes Q τ g) :
    Computes (P ++ Q ++ P.inv ++ Q.inv) (σ * τ * σ⁻¹ * τ⁻¹) (fun x => f x && g x) := by
  intro x
  simp only [BProg.eval_append, BProg.eval_inv, h1 x, h2 x]
  rcases Bool.eq_false_or_eq_true (f x) with hf | hf <;>
    rcases Bool.eq_false_or_eq_true (g x) with hg | hg <;>
      simp only [hf, hg] <;> simp

theorem length_comb (P Q : BProg) :
    (P ++ Q ++ P.inv ++ Q.inv).length = 2 * (P.length + Q.length) := by
  simp [BProg.inv]; ring

theorem comb_ne_nil {P Q : BProg} (hP : P ≠ []) : P ++ Q ++ P.inv ++ Q.inv ≠ [] := by
  simp only [ne_eq, List.append_eq_nil_iff, not_and]
  intro h; exact absurd h.1.1 hP

theorem length_bound {da db lP lQ : ℕ} (hP : lP ≤ 4 ^ da) (hQ : lQ ≤ 4 ^ db) :
    2 * (lP + lQ) ≤ 4 ^ (max da db + 1) := by
  have h1 : (4:ℕ) ^ da ≤ 4 ^ (max da db) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h2 : (4:ℕ) ^ db ≤ 4 ^ (max da db) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have h3 : (4:ℕ) ^ (max da db + 1) = 4 * 4 ^ (max da db) := by ring
  omega

/-- **Barrington's theorem.**  Every Boolean circuit of depth `d` is computed, with respect
to any prescribed five-cycle `γ`, by a width-5 permutation branching program of length at
most `4 ^ d`. -/
theorem exists_bprog (c : Circuit) : ∀ γ : Perm (Fin 5), Conj5 γ →
    ∃ P : BProg, P ≠ [] ∧ P.length ≤ 4 ^ c.depth ∧ Computes P γ c.eval := by
  induction c with
  | const b =>
      intro γ _
      refine ⟨[(0, if b then γ else 1, if b then γ else 1)], by simp, by simp [Circuit.depth], ?_⟩
      intro x
      simp only [BProg.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Instr.run, mul_one, Circuit.eval]
      split <;> rfl
  | var i =>
      intro γ _
      refine ⟨[(i, γ, 1)], by simp, by simp [Circuit.depth], ?_⟩
      intro x
      simp only [BProg.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Instr.run, mul_one, Circuit.eval]
  | not c ih =>
      intro γ hγ
      obtain ⟨P, hne, hlen, hP⟩ := ih γ⁻¹ hγ.inv
      refine ⟨P.pre γ, BProg.pre_ne_nil γ hne, ?_, ?_⟩
      · rw [BProg.length_pre]
        exact hlen.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      · intro x; exact neg_computes hne hP x
  | and a b iha ihb =>
      intro γ hγ
      obtain ⟨σ, τ, hσ, hτ, hc⟩ := hγ.commutator
      obtain ⟨P, hPne, hPlen, hP⟩ := iha σ hσ
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ihb τ hτ
      refine ⟨P ++ Q ++ P.inv ++ Q.inv, comb_ne_nil hPne, ?_, ?_⟩
      · rw [length_comb]
        exact length_bound hPlen hQlen
      · intro x
        have h := and_computes hP hQ x
        rw [hc] at h
        exact h
  | or a b iha ihb =>
      intro γ hγ
      obtain ⟨σ, τ, hσ, hτ, hc⟩ := hγ.inv.commutator
      obtain ⟨P, hPne, hPlen, hP⟩ := iha σ⁻¹ hσ.inv
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ihb τ⁻¹ hτ.inv
      have hP' : Computes (P.pre σ) σ (fun x => !a.eval x) := neg_computes hPne hP
      have hQ' : Computes (Q.pre τ) τ (fun x => !b.eval x) := neg_computes hQne hQ
      have hne' : (P.pre σ) ++ (Q.pre τ) ++ (P.pre σ).inv ++ (Q.pre τ).inv ≠ [] :=
        comb_ne_nil (BProg.pre_ne_nil σ hPne)
      refine ⟨(((P.pre σ) ++ (Q.pre τ) ++ (P.pre σ).inv ++ (Q.pre τ).inv).pre γ),
        BProg.pre_ne_nil γ hne', ?_, ?_⟩
      · rw [BProg.length_pre, length_comb, BProg.length_pre, BProg.length_pre]
        exact length_bound hPlen hQlen
      · have hand := and_computes hP' hQ'
        rw [hc] at hand
        intro x
        have h := neg_computes hne' hand x
        simp only [Bool.not_and, Bool.not_not] at h
        exact h

/-! ## The easy direction: simulating a branching program by a shallow circuit -/

theorem exists_fin5 (p : Fin 5 → Prop) : (∃ i, p i) ↔ p 0 ∨ p 1 ∨ p 2 ∨ p 3 ∨ p 4 := by
  constructor
  · rintro ⟨i, hi⟩; fin_cases i <;> tauto
  · rintro (h | h | h | h | h) <;> exact ⟨_, h⟩

theorem forall_fin5 (p : Fin 5 → Prop) : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 ∧ p 4 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i; fin_cases i <;> assumption

/-- A balanced disjunction of five circuits. -/
def orAll (f : Fin 5 → Circuit) : Circuit :=
  (((f 0).or (f 1)).or ((f 2).or (f 3))).or (f 4)

/-- A balanced conjunction of five circuits. -/
def andAll (f : Fin 5 → Circuit) : Circuit :=
  (((f 0).and (f 1)).and ((f 2).and (f 3))).and (f 4)

theorem eval_orAll (f : Fin 5 → Circuit) (x : ℕ → Bool) :
    (orAll f).eval x = decide (∃ i, (f i).eval x = true) := by
  simp [orAll, Circuit.eval, exists_fin5, Bool.or_assoc]

theorem eval_andAll (f : Fin 5 → Circuit) (x : ℕ → Bool) :
    (andAll f).eval x = decide (∀ i, (f i).eval x = true) := by
  simp [andAll, Circuit.eval, forall_fin5, Bool.and_assoc]

theorem depth_orAll {f : Fin 5 → Circuit} {d : ℕ} (h : ∀ i, (f i).depth ≤ d) :
    (orAll f).depth ≤ d + 3 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [orAll, Circuit.depth]
  omega

theorem depth_andAll {f : Fin 5 → Circuit} {d : ℕ} (h : ∀ i, (f i).depth ≤ d) :
    (andAll f).depth ≤ d + 3 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [andAll, Circuit.depth]
  omega

/-- The circuit computing the `(i, j)` entry of the permutation matrix of one instruction. -/
def matOne (t : Instr) (i j : Fin 5) : Circuit :=
  ((Circuit.var t.1).and (Circuit.const (decide (t.2.1 i = j)))).or
    ((Circuit.var t.1).not.and (Circuit.const (decide (t.2.2 i = j))))

/-- The circuits for programs of length at most one. -/
def matBase : BProg → Fin 5 → Fin 5 → Circuit
  | [] => fun i j => Circuit.const (decide (i = j))
  | t :: _ => matOne t

/-- Circuits computing the entries `(i,j)` (i.e. the bit `P.eval x i = j`) of the
permutation computed by a program of length at most `2 ^ k`. -/
def mat : ℕ → BProg → Fin 5 → Fin 5 → Circuit
  | 0, P => matBase P
  | k + 1, P => fun i j =>
      orAll fun l => (mat k (P.drop (2 ^ k)) i l).and (mat k (P.take (2 ^ k)) l j)

theorem depth_mat (k : ℕ) : ∀ (P : BProg) (i j : Fin 5), (mat k P i j).depth ≤ 4 * k + 3 := by
  induction k with
  | zero =>
      intro P i j
      cases P <;> simp [mat, matBase, matOne, Circuit.depth]
  | succ k ih =>
      intro P i j
      have h : ∀ l : Fin 5,
          ((mat k (P.drop (2 ^ k)) i l).and (mat k (P.take (2 ^ k)) l j)).depth ≤ 4 * k + 4 := by
        intro l
        have h1 := ih (P.drop (2 ^ k)) i l
        have h2 := ih (P.take (2 ^ k)) l j
        simp only [Circuit.depth]
        omega
      have hor := depth_orAll h
      simp only [mat]
      omega

theorem eval_mat (k : ℕ) : ∀ P : BProg, P.length ≤ 2 ^ k → ∀ (x : ℕ → Bool) (i j : Fin 5),
    (mat k P i j).eval x = decide (P.eval x i = j) := by
  induction k with
  | zero =>
      intro P hP x i j
      match P with
      | [] => simp [mat, matBase, BProg.eval, Circuit.eval]
      | [t] =>
          cases ht : x t.1 <;>
            simp [mat, matBase, matOne, BProg.eval, Circuit.eval, Instr.run, ht]
      | t :: u :: r => simp at hP
  | succ k ih =>
      intro P hP x i j
      have hsplit : P.take (2 ^ k) ++ P.drop (2 ^ k) = P := List.take_append_drop _ _
      have h1 : (P.take (2 ^ k)).length ≤ 2 ^ k := by simp
      have h2 : (P.drop (2 ^ k)).length ≤ 2 ^ k := by
        have : P.length ≤ 2 ^ k + 2 ^ k := by
          have : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        simp only [List.length_drop]
        omega
      have hPe : P.eval x = BProg.eval (P.take (2 ^ k)) x * BProg.eval (P.drop (2 ^ k)) x := by
        conv_lhs => rw [← hsplit]
        exact BProg.eval_append _ _ x
      simp only [mat, eval_orAll, Circuit.eval, Bool.and_eq_true, ih _ h1, ih _ h2,
        decide_eq_true_eq, hPe, Equiv.Perm.mul_apply, decide_eq_decide]
      constructor
      · rintro ⟨l, hl1, hl2⟩
        rw [hl1]; exact hl2
      · intro h
        exact ⟨_, rfl, h⟩

/-- Every width-5 permutation branching program of length `L` is simulated by a Boolean
circuit of depth at most `4 * ⌈log₂ L⌉ + 6`. -/
theorem exists_circuit (P : BProg) (γ : Perm (Fin 5)) :
    ∃ c : Circuit, c.depth ≤ 4 * Nat.clog 2 P.length + 6 ∧
      ∀ x, c.eval x = decide (P.eval x = γ) := by
  have hk : P.length ≤ 2 ^ Nat.clog 2 P.length := Nat.le_pow_clog (by norm_num) _
  refine ⟨andAll fun i => mat (Nat.clog 2 P.length) P i (γ i), ?_, ?_⟩
  · have := depth_andAll (fun i => depth_mat (Nat.clog 2 P.length) P i (γ i))
    omega
  · intro x
    rw [eval_andAll]
    simp only [eval_mat _ P hk x, decide_eq_true_eq, decide_eq_decide]
    exact (Equiv.ext_iff).symm

/-! ## Barrington's theorem -/

/-- **Barrington's theorem: `NC¹` equals width-5 permutation branching programs.**

* Any Boolean circuit of depth `d` is computed by a width-5 permutation branching program
  of length at most `4 ^ d` (the program outputs a fixed five-cycle `γ` exactly on the
  accepted inputs, and the identity elsewhere).
* Conversely, any width-5 permutation branching program of length `L` — read as accepting
  the inputs on which its output is a prescribed permutation `γ` — is computed by a Boolean
  circuit of depth at most `4 * ⌈log₂ L⌉ + 6`.

Thus depth `O(log n)` circuits correspond exactly to branching programs of polynomial
length. -/
theorem barrington :
    (∀ (c : Circuit) (γ : Perm (Fin 5)), Conj5 γ →
        ∃ P : BProg, P.length ≤ 4 ^ c.depth ∧ ∀ x, P.eval x = if c.eval x then γ else 1) ∧
    (∀ (P : BProg) (γ : Perm (Fin 5)),
        ∃ c : Circuit, c.depth ≤ 4 * Nat.clog 2 P.length + 6 ∧
          ∀ x, c.eval x = decide (P.eval x = γ)) := by
  refine ⟨fun c γ hγ => ?_, exists_circuit⟩
  obtain ⟨P, -, hlen, hP⟩ := exists_bprog c γ hγ
  exact ⟨P, hlen, hP⟩

end CS

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

