/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise Barrington's theorem in the following form.

* A Boolean function family `f n : (Fin n → Bool) → Bool` is *in NC¹* (`CS.InNC1`) when it is
  computed by Boolean formulas (constants, `¬`, fan-in-two `∧`, `∨`) of depth `O(log n)`.
  A formula of depth `d` has at most `2 ^ d` leaves, so this is the usual class of
  logarithmic-depth fan-in-two circuits / polynomial-size formulas.
* A *width-5 permutation branching program* (`CS.Prog`) is a finite sequence of instructions,
  each of which queries one input variable and applies one of two permutations of the five
  states `Fin 5`; the program computes the ordered product of these permutations, and accepts
  an input when the image of the start state `0` lies in a designated set of accepting states.
  `CS.InW5BP` asks for such programs of polynomial length.

The main theorem `CS.barrington` states that the two classes coincide. The two directions are
proved with explicit resource bounds: a formula of depth `d` is turned into a program of length
at most `4 ^ d` (`CS.exists_prog`, via the 5-cycle commutator construction `CS.exists_comp`),
and a program of length at most `2 ^ k` is simulated by a formula of depth at most `4 * k + 4`
(`CS.progFormula_eval`, `CS.progFormula_depth`, via a balanced divide-and-conquer evaluation of
the product of the instruction permutations).
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

/-! ## Boolean formulas (the NC¹ side) -/

/-- Boolean formulas over variables indexed by `α`, with constants, negation and
fan-in-two conjunction and disjunction. -/
inductive Formula (α : Type*) where
  | const : Bool → Formula α
  | var : α → Formula α
  | not : Formula α → Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  deriving Inhabited

namespace Formula

variable {α : Type*}

/-- The Boolean function computed by a formula. -/
def eval : Formula α → (α → Bool) → Bool
  | const b, _ => b
  | var i, x => x i
  | not F, x => !(F.eval x)
  | and F G, x => (F.eval x) && (G.eval x)
  | or F G, x => (F.eval x) || (G.eval x)

/-- The depth of a formula (its number of levels of gates). -/
def depth : Formula α → ℕ
  | const _ => 0
  | var _ => 0
  | not F => F.depth + 1
  | and F G => max F.depth G.depth + 1
  | or F G => max F.depth G.depth + 1

end Formula

/-! ## Width-5 permutation branching programs -/

/-- The symmetric group on five points, the "width 5" state space. -/
abbrev S5 := Equiv.Perm (Fin 5)

/-- One instruction of a width-5 permutation branching program: it queries the
variable `idx` and applies the permutation `on0` or `on1` according to the answer. -/
structure Instr (α : Type*) where
  /-- the queried variable -/
  idx : α
  /-- permutation applied if the queried bit is `false` -/
  on0 : S5
  /-- permutation applied if the queried bit is `true` -/
  on1 : S5

variable {α : Type*}

/-- The permutation performed by an instruction on a given input. -/
def Instr.apply (I : Instr α) (x : α → Bool) : S5 := if x I.idx then I.on1 else I.on0

/-- The permutation performed by a list of instructions: the ordered product. -/
def instrsPerm (l : List (Instr α)) (x : α → Bool) : S5 := (l.map (fun I => I.apply x)).prod

/-- A width-5 permutation branching program: a sequence of instructions together with
a set of accepting final states. -/
structure Prog (α : Type*) where
  /-- the instruction sequence -/
  instrs : List (Instr α)
  /-- the accepting states -/
  acc : Finset (Fin 5)

/-- The length of a branching program. -/
def Prog.length (P : Prog α) : ℕ := P.instrs.length

/-- The permutation computed by a program on a given input. -/
def Prog.perm (P : Prog α) (x : α → Bool) : S5 := instrsPerm P.instrs x

/-- The program accepts when the image of the start state `0` under the computed
permutation is an accepting state. -/
def Prog.accepts (P : Prog α) (x : α → Bool) : Bool := decide (P.perm x 0 ∈ P.acc)

/-! ## The two complexity classes -/

/-- `f` is in NC¹: it is computed by a family of Boolean formulas of depth `O(log n)`
(equivalently, by fan-in-two circuits of logarithmic depth / polynomial-size formulas). -/
def InNC1 (f : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ (F : (n : ℕ) → Formula (Fin n)) (c : ℕ),
    (∀ n x, (F n).eval x = f n x) ∧ ∀ n, (F n).depth ≤ c * (Nat.log 2 n + 1)

/-- `f` is computed by a family of polynomial-length width-5 permutation branching
programs. -/
def InW5BP (f : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ (P : (n : ℕ) → Prog (Fin n)) (c k : ℕ),
    (∀ n x, (P n).accepts x = f n x) ∧ ∀ n, (P n).length ≤ c * (n + 1) ^ k

/-! ## Basic facts about `instrsPerm` -/

@[simp] lemma instrsPerm_nil (x : α → Bool) : instrsPerm ([] : List (Instr α)) x = 1 := rfl

@[simp] lemma instrsPerm_cons (I : Instr α) (l : List (Instr α)) (x : α → Bool) :
    instrsPerm (I :: l) x = I.apply x * instrsPerm l x := rfl

lemma instrsPerm_append (l₁ l₂ : List (Instr α)) (x : α → Bool) :
    instrsPerm (l₁ ++ l₂) x = instrsPerm l₁ x * instrsPerm l₂ x := by
  simp [instrsPerm, List.map_append, List.prod_append]

/-! ## Five-cycles -/

/-- A distinguished 5-cycle. -/
def gamma0 : S5 := c[(0 : Fin 5), 2, 1, 4, 3]

/-- Being a 5-cycle, defined as being conjugate to `gamma0`. -/
def IsFive (σ : S5) : Prop := ∃ p : S5, p * gamma0 * p⁻¹ = σ

lemma isFive_gamma0 : IsFive gamma0 := ⟨1, by group⟩

lemma IsFive.conj {σ : S5} (h : IsFive σ) (p : S5) : IsFive (p * σ * p⁻¹) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨p * q, by rw [← hq]; group⟩

private lemma gamma0_inv_conj :
    (c[(1 : Fin 5), 4] * c[(2 : Fin 5), 3]) * gamma0 * ((c[(1 : Fin 5), 4] * c[(2 : Fin 5), 3]))⁻¹
      = gamma0⁻¹ := by decide

lemma IsFive.inv {σ : S5} (h : IsFive σ) : IsFive σ⁻¹ := by
  obtain ⟨q, hq⟩ := h
  set r : S5 := c[(1 : Fin 5), 4] * c[(2 : Fin 5), 3] with hr
  refine ⟨q * r, ?_⟩
  calc (q * r) * gamma0 * (q * r)⁻¹ = q * (r * gamma0 * r⁻¹) * q⁻¹ := by group
    _ = q * gamma0⁻¹ * q⁻¹ := by rw [hr, gamma0_inv_conj]
    _ = (q * gamma0 * q⁻¹)⁻¹ := by group
    _ = σ⁻¹ := by rw [hq]

lemma IsFive.ne_one {σ : S5} (h : IsFive σ) : σ ≠ 1 := by
  obtain ⟨q, hq⟩ := h
  rw [← hq]
  intro hc
  have : gamma0 = 1 := by
    have := congrArg (fun z => q⁻¹ * z * q) hc
    simpa [mul_assoc] using this
  exact absurd this (by decide)

lemma IsFive.apply_zero_ne {σ : S5} (h : IsFive σ) : σ 0 ≠ 0 := by
  obtain ⟨q, hq⟩ := h
  rw [← hq]
  simp only [Equiv.Perm.mul_apply]
  intro hc
  have : gamma0 (q⁻¹ 0) = q⁻¹ 0 := by
    have := congrArg (fun z => q⁻¹ z) hc
    simpa using this
  revert this
  generalize q⁻¹ 0 = a
  revert a
  decide

/-- Every 5-cycle is a commutator of two 5-cycles. -/
lemma exists_commutator {γ : S5} (h : IsFive γ) :
    ∃ σ τ : S5, IsFive σ ∧ IsFive τ ∧ σ * τ * σ⁻¹ * τ⁻¹ = γ := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹, q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹, ?_, ?_, ?_⟩
  · exact ⟨q * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]), by
      have h1 : (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]) * gamma0
          * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4])⁻¹ = c[(0 : Fin 5), 1, 2, 3, 4] := by decide
      calc (q * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4])) * gamma0
            * (q * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]))⁻¹
          = q * ((c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]) * gamma0
              * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4])⁻¹) * q⁻¹ := by group
        _ = q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹ := by rw [h1]⟩
  · exact ⟨q * c[(1 : Fin 5), 3, 4], by
      have h1 : c[(1 : Fin 5), 3, 4] * gamma0 * (c[(1 : Fin 5), 3, 4])⁻¹
          = c[(0 : Fin 5), 2, 3, 1, 4] := by decide
      calc (q * c[(1 : Fin 5), 3, 4]) * gamma0 * (q * c[(1 : Fin 5), 3, 4])⁻¹
          = q * (c[(1 : Fin 5), 3, 4] * gamma0 * (c[(1 : Fin 5), 3, 4])⁻¹) * q⁻¹ := by group
        _ = q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹ := by rw [h1]⟩
  · have h2 : c[(0 : Fin 5), 1, 2, 3, 4] * c[(0 : Fin 5), 2, 3, 1, 4]
        * (c[(0 : Fin 5), 1, 2, 3, 4])⁻¹ * (c[(0 : Fin 5), 2, 3, 1, 4])⁻¹ = gamma0 := by decide
    calc (q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹) * (q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹)
          * (q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹)⁻¹ * (q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹)⁻¹
        = q * (c[(0 : Fin 5), 1, 2, 3, 4] * c[(0 : Fin 5), 2, 3, 1, 4]
            * (c[(0 : Fin 5), 1, 2, 3, 4])⁻¹ * (c[(0 : Fin 5), 2, 3, 1, 4])⁻¹) * q⁻¹ := by group
      _ = q * gamma0 * q⁻¹ := by rw [h2]
      _ = γ := hq

/-! ## Barrington's construction: formulas to branching programs -/

/-- `Comp l σ g` says the instruction list `l` computes the Boolean function `g` in the
sense of Barrington: the product of the instruction permutations is `σ` when `g` holds
and the identity otherwise. -/
def Comp (l : List (Instr α)) (σ : S5) (g : (α → Bool) → Bool) : Prop :=
  ∀ x, instrsPerm l x = if g x then σ else 1

lemma Comp.congr {l : List (Instr α)} {σ : S5} {g g' : (α → Bool) → Bool}
    (h : Comp l σ g) (hg : ∀ x, g x = g' x) : Comp l σ g' := by
  intro x; rw [h x, hg x]

lemma comp_mul_head {l : List (Instr α)} (hl : l ≠ []) (ρ : S5) :
    ∃ l' : List (Instr α), l'.length = l.length ∧ l' ≠ [] ∧
      ∀ x, instrsPerm l' x = ρ * instrsPerm l x := by
  cases l with
  | nil => exact absurd rfl hl
  | cons I rest =>
      refine ⟨⟨I.idx, ρ * I.on0, ρ * I.on1⟩ :: rest, by simp, by simp, fun x => ?_⟩
      simp only [instrsPerm_cons, Instr.apply]
      by_cases hx : x I.idx <;> simp [hx, mul_assoc]

lemma comp_and {l₁ l₂ l₃ l₄ : List (Instr α)} {σ τ : S5} {g h : (α → Bool) → Bool}
    (h₁ : Comp l₁ σ g) (h₂ : Comp l₂ τ h) (h₃ : Comp l₃ σ⁻¹ g) (h₄ : Comp l₄ τ⁻¹ h) :
    Comp (l₁ ++ l₂ ++ l₃ ++ l₄) (σ * τ * σ⁻¹ * τ⁻¹) (fun x => g x && h x) := by
  intro x
  simp only [instrsPerm_append, h₁ x, h₂ x, h₃ x, h₄ x]
  by_cases hg : g x = true <;> by_cases hh : h x = true <;> simp [hg, hh, mul_assoc]

lemma comp_not {l : List (Instr α)} {σ : S5} {g : (α → Bool) → Bool} (hne : l ≠ [])
    (h : Comp l σ⁻¹ g) : ∃ l' : List (Instr α), l'.length = l.length ∧ l' ≠ [] ∧
      Comp l' σ (fun x => !g x) := by
  obtain ⟨l', hlen, hne', hval⟩ := comp_mul_head hne σ
  refine ⟨l', hlen, hne', fun x => ?_⟩
  rw [hval, h x]
  by_cases hg : g x = true <;> simp [hg]

/-- Barrington's theorem, main construction: a formula of depth `d` is computed, for any
target 5-cycle, by a nonempty instruction list of length at most `4 ^ d`. -/
lemma exists_comp (a₀ : α) (F : Formula α) :
    ∀ σ : S5, IsFive σ → ∃ l : List (Instr α), l ≠ [] ∧ l.length ≤ 4 ^ F.depth ∧
      Comp l σ F.eval := by
  induction F with
  | const b =>
      intro σ _
      refine ⟨[⟨a₀, if b then σ else 1, if b then σ else 1⟩], by simp, by simp [Formula.depth], ?_⟩
      intro x
      simp [instrsPerm, Instr.apply, Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[⟨i, 1, σ⟩], by simp, by simp [Formula.depth], ?_⟩
      intro x
      by_cases hx : x i <;> simp [instrsPerm, Instr.apply, Formula.eval, hx]
  | not F ih =>
      intro σ hσ
      obtain ⟨l, hne, hlen, hc⟩ := ih σ⁻¹ hσ.inv
      obtain ⟨l', hlen', hne', hc'⟩ := comp_not hne (by rw [inv_inv]; exact hc)
      refine ⟨l', hne', ?_, hc'.congr (fun _ => rfl)⟩
      rw [hlen']
      exact hlen.trans (Nat.pow_le_pow_right (by norm_num) (by simp [Formula.depth]))
  | and F G ihF ihG =>
      intro σ hσ
      obtain ⟨s, t, hs, ht, hst⟩ := exists_commutator hσ
      obtain ⟨l₁, h1ne, h1len, h1⟩ := ihF s hs
      obtain ⟨l₂, _, h2len, h2⟩ := ihG t ht
      obtain ⟨l₃, _, h3len, h3⟩ := ihF s⁻¹ hs.inv
      obtain ⟨l₄, _, h4len, h4⟩ := ihG t⁻¹ ht.inv
      refine ⟨l₁ ++ l₂ ++ l₃ ++ l₄, by simp [h1ne], ?_, ?_⟩
      · have hF : (4 : ℕ) ^ F.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hG : (4 : ℕ) ^ G.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have hd : (4 : ℕ) ^ (Formula.depth (F.and G)) = 4 * 4 ^ (max F.depth G.depth) := by
          simp [Formula.depth, pow_succ, mul_comm]
        simp only [List.length_append, hd]
        omega
      · have hcomb := comp_and h1 h2 h3 h4
        rw [hst] at hcomb
        exact hcomb.congr (fun _ => rfl)
  | or F G ihF ihG =>
      intro σ hσ
      obtain ⟨s, t, hs, ht, hst⟩ := exists_commutator hσ.inv
      obtain ⟨a₁, a1ne, a1len, a1⟩ := ihF s⁻¹ hs.inv
      obtain ⟨l₁, k1len, k1ne, k1⟩ := comp_not a1ne (by rw [inv_inv]; exact a1)
      obtain ⟨a₂, a2ne, a2len, a2⟩ := ihG t⁻¹ ht.inv
      obtain ⟨l₂, k2len, k2ne, k2⟩ := comp_not a2ne (by rw [inv_inv]; exact a2)
      obtain ⟨a₃, a3ne, a3len, a3⟩ := ihF s hs
      obtain ⟨l₃, k3len, _, k3⟩ := comp_not (σ := s⁻¹) a3ne (by rw [inv_inv]; exact a3)
      obtain ⟨a₄, a4ne, a4len, a4⟩ := ihG t ht
      obtain ⟨l₄, k4len, _, k4⟩ := comp_not (σ := t⁻¹) a4ne (by rw [inv_inv]; exact a4)
      simp only [inv_inv] at k1 k2
      have hcomb := comp_and k1 k2 k3 k4
      rw [hst] at hcomb
      obtain ⟨L, hLlen, hLne, hL⟩ := comp_not (σ := σ) (by simp [k1ne]) hcomb
      refine ⟨L, hLne, ?_, hL.congr (fun x => by simp [Formula.eval])⟩
      have hF : (4 : ℕ) ^ F.depth ≤ 4 ^ (max F.depth G.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hG : (4 : ℕ) ^ G.depth ≤ 4 ^ (max F.depth G.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hd : (4 : ℕ) ^ (Formula.depth (F.or G)) = 4 * 4 ^ (max F.depth G.depth) := by
        simp [Formula.depth, pow_succ, mul_comm]
      rw [hLlen, hd]
      simp only [List.length_append, k1len, k2len, k3len, k4len]
      omega

/-- From a formula to a width-5 branching program of length at most `4 ^ depth`. -/
lemma exists_prog (n : ℕ) (F : Formula (Fin n)) :
    ∃ P : Prog (Fin n), P.length ≤ 4 ^ F.depth ∧ ∀ x, P.accepts x = F.eval x := by
  cases n with
  | zero =>
      refine ⟨⟨[], if F.eval (fun i => i.elim0) then Finset.univ else ∅⟩,
        by simp [Prog.length], ?_⟩
      intro x
      have hx : x = (fun i => i.elim0) := Subsingleton.elim _ _
      subst hx
      by_cases hF : F.eval (fun i : Fin 0 => i.elim0) = true <;>
        simp [Prog.accepts, Prog.perm, hF]
  | succ m =>
      obtain ⟨l, -, hlen, hc⟩ :=
        exists_comp (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) F gamma0 isFive_gamma0
      refine ⟨⟨l, {gamma0 0}⟩, hlen, ?_⟩
      intro x
      have hz : ¬ (0 : Fin 5) = gamma0 0 := by decide
      by_cases hF : F.eval x = true
      · simp [Prog.accepts, Prog.perm, hc x, hF]
      · simp only [Bool.not_eq_true] at hF
        simp [Prog.accepts, Prog.perm, hc x, hF, hz]

/-! ## The converse: simulating branching programs by shallow formulas -/

/-- A balanced disjunction of five formulas. -/
def orAll5 (g : Fin 5 → Formula α) : Formula α :=
  .or (.or (.or (g 0) (g 1)) (.or (g 2) (g 3))) (g 4)

lemma orAll5_eval (g : Fin 5 → Formula α) (x : α → Bool) :
    (orAll5 g).eval x = decide (∃ i : Fin 5, (g i).eval x = true) := by
  rw [Bool.eq_iff_iff]
  simp only [orAll5, Formula.eval, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((h | h) | (h | h)) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩]
  · rintro ⟨i, hi⟩
    fin_cases i <;> tauto

lemma orAll5_depth {g : Fin 5 → Formula α} {d : ℕ} (h : ∀ i, (g i).depth ≤ d) :
    (orAll5 g).depth ≤ d + 3 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [orAll5, Formula.depth]
  omega

/-- A `5 × 5` matrix of formulas, describing a permutation-valued function. -/
abbrev Mat (α : Type*) := Fin 5 → Fin 5 → Formula α

/-- `Represents M e` : the entry `M i j` computes the predicate `e x i = j`. -/
def Represents (M : Mat α) (e : (α → Bool) → S5) : Prop :=
  ∀ x i j, (M i j).eval x = decide (e x i = j)

/-- The identity matrix. -/
def matId : Mat α := fun i j => .const (decide (i = j))

/-- The matrix of a single instruction. -/
def matOfInstr (I : Instr α) : Mat α := fun i j =>
  if I.on0 i = j then (if I.on1 i = j then .const true else .not (.var I.idx))
  else (if I.on1 i = j then .var I.idx else .const false)

/-- Boolean matrix product; `matComp A B` represents "`A` then `B`". -/
def matComp (A B : Mat α) : Mat α := fun i j => orAll5 (fun k => .and (A i k) (B k j))

lemma matId_represents : Represents (matId : Mat α) (fun _ => 1) := by
  intro x i j
  simp [matId, Formula.eval]

lemma matOfInstr_represents (I : Instr α) :
    Represents (matOfInstr I) (fun x => instrsPerm [I] x) := by
  intro x i j
  simp only [matOfInstr, instrsPerm, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Instr.apply]
  by_cases hx : x I.idx = true <;> by_cases h0 : I.on0 i = j <;> by_cases h1 : I.on1 i = j <;>
    simp [hx, h0, h1, Formula.eval]

lemma matComp_represents {A B : Mat α} {a b : (α → Bool) → S5}
    (hA : Represents A a) (hB : Represents B b) :
    Represents (matComp A B) (fun x => b x * a x) := by
  intro x i j
  simp only [matComp]
  rw [orAll5_eval, Bool.eq_iff_iff]
  simp only [Formula.eval, hA x i, hB x _ j, Bool.and_eq_true, decide_eq_true_eq,
    Equiv.Perm.mul_apply]
  constructor
  · rintro ⟨k, hk1, hk2⟩
    exact hk1 ▸ hk2
  · intro h
    exact ⟨a x i, rfl, h⟩

/-- The divide-and-conquer simulation of an instruction list by a matrix of formulas.
`k` is a budget: the result is correct as soon as `l.length ≤ 2 ^ k`. -/
def sim : ℕ → List (Instr α) → Mat α
  | 0, [] => matId
  | 0, (I :: _) => matOfInstr I
  | (k + 1), l => matComp (sim k (l.drop (l.length / 2))) (sim k (l.take (l.length / 2)))

lemma sim_depth (k : ℕ) (l : List (Instr α)) (i j : Fin 5) :
    ((sim k l) i j).depth ≤ 4 * k + 1 := by
  induction k generalizing l i j with
  | zero =>
      cases l with
      | nil => simp [sim, matId, Formula.depth]
      | cons I rest =>
          simp only [sim, matOfInstr]
          split <;> split <;> simp [Formula.depth]
  | succ k ih =>
      simp only [sim, matComp]
      have hb : ∀ m : Fin 5, (Formula.and ((sim k (l.drop (l.length / 2))) i m)
          ((sim k (l.take (l.length / 2))) m j)).depth ≤ 4 * k + 2 := by
        intro m
        have h1 := ih (l.drop (l.length / 2)) i m
        have h2 := ih (l.take (l.length / 2)) m j
        simp only [Formula.depth]
        omega
      have := orAll5_depth hb
      omega

lemma sim_represents (k : ℕ) (l : List (Instr α)) (hl : l.length ≤ 2 ^ k) :
    Represents (sim k l) (instrsPerm l) := by
  induction k generalizing l with
  | zero =>
      cases l with
      | nil =>
          intro x i j
          simp [sim, matId, Formula.eval, instrsPerm]
      | cons I rest =>
          have hr : rest = [] := by
            simp only [List.length_cons, pow_zero] at hl
            exact List.length_eq_zero_iff.mp (by omega)
          subst hr
          simpa [sim] using matOfInstr_represents I
  | succ k ih =>
      have h2k : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      have hd : (l.drop (l.length / 2)).length ≤ 2 ^ k := by
        simp only [List.length_drop]; omega
      have ht : (l.take (l.length / 2)).length ≤ 2 ^ k := by
        simp only [List.length_take]; omega
      have h := matComp_represents (ih _ hd) (ih _ ht)
      have heq : (fun x => instrsPerm (l.take (l.length / 2)) x *
            instrsPerm (l.drop (l.length / 2)) x) = instrsPerm l := by
        funext x
        rw [← instrsPerm_append, List.take_append_drop]
      simp only [sim]
      rw [← heq]
      exact h

/-- The formula simulating a whole program. -/
def progFormula (P : Prog α) (k : ℕ) : Formula α :=
  orAll5 (fun j => if j ∈ P.acc then (sim k P.instrs) 0 j else .const false)

lemma progFormula_depth (P : Prog α) (k : ℕ) : (progFormula P k).depth ≤ 4 * k + 4 := by
  have hb : ∀ j : Fin 5, (if j ∈ P.acc then (sim k P.instrs) 0 j
      else (Formula.const false : Formula α)).depth ≤ 4 * k + 1 := by
    intro j
    split
    · exact sim_depth k P.instrs 0 j
    · simp [Formula.depth]
  have := orAll5_depth hb
  simp only [progFormula]
  omega

lemma progFormula_eval (P : Prog α) (k : ℕ) (hk : P.length ≤ 2 ^ k) (x : α → Bool) :
    (progFormula P k).eval x = P.accepts x := by
  have hrep := sim_represents k P.instrs hk
  rw [progFormula, orAll5_eval, Bool.eq_iff_iff]
  simp only [Prog.accepts, decide_eq_true_eq, Prog.perm]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hja : j ∈ P.acc
    · rw [if_pos hja, hrep x 0 j] at hj
      simp only [decide_eq_true_eq] at hj
      rwa [hj]
    · rw [if_neg hja] at hj
      simp [Formula.eval] at hj
  · intro h
    refine ⟨instrsPerm P.instrs x 0, ?_⟩
    rw [if_pos h, hrep x 0 _]
    simp

/-! ## Putting it together -/

private lemma log_two_succ_le (n : ℕ) : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := by
  have h1 : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  calc Nat.log 2 (n + 1) ≤ Nat.log 2 (2 ^ (Nat.log 2 n + 1)) := Nat.log_mono_right h1
    _ = Nat.log 2 n + 1 := by simp [Nat.log_pow]

theorem nc1_of_w5bp (f : (n : ℕ) → (Fin n → Bool) → Bool) (h : InW5BP f) : InNC1 f := by
  obtain ⟨P, c, k, hPf, hPlen⟩ := h
  set A : ℕ := Nat.log 2 c + 1 with hA
  set K : ℕ → ℕ := fun n => A + k * (Nat.log 2 (n + 1) + 1) with hK
  refine ⟨fun n => progFormula (P n) (K n), 4 * (A + 2 * k) + 4, fun n x => ?_, fun n => ?_⟩
  · have hlen : (P n).length ≤ 2 ^ (K n) := by
      have hc : c < 2 ^ A := Nat.lt_pow_succ_log_self (by norm_num) c
      have hn : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
      calc (P n).length ≤ c * (n + 1) ^ k := hPlen n
        _ ≤ 2 ^ A * (2 ^ (Nat.log 2 (n + 1) + 1)) ^ k :=
            Nat.mul_le_mul (le_of_lt hc) (Nat.pow_le_pow_left (le_of_lt hn) k)
        _ = 2 ^ (K n) := by rw [← pow_mul, ← pow_add, hK]; ring_nf
    show (progFormula (P n) (K n)).eval x = f n x
    rw [progFormula_eval (P n) (K n) hlen x, hPf n x]
  · show (progFormula (P n) (K n)).depth ≤ (4 * (A + 2 * k) + 4) * (Nat.log 2 n + 1)
    have hd := progFormula_depth (P n) (K n)
    have hlog := log_two_succ_le n
    have hKle : K n ≤ (A + 2 * k) * (Nat.log 2 n + 1) := by
      have h1 : Nat.log 2 (n + 1) + 1 ≤ 2 * (Nat.log 2 n + 1) := by omega
      have h2 : A ≤ A * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right _ (by omega)
      calc K n = A + k * (Nat.log 2 (n + 1) + 1) := rfl
        _ ≤ A * (Nat.log 2 n + 1) + k * (2 * (Nat.log 2 n + 1)) :=
            Nat.add_le_add h2 (Nat.mul_le_mul_left _ h1)
        _ = (A + 2 * k) * (Nat.log 2 n + 1) := by ring
    have h3 : (4 * (A + 2 * k) + 4) * (Nat.log 2 n + 1)
        = 4 * ((A + 2 * k) * (Nat.log 2 n + 1)) + 4 * (Nat.log 2 n + 1) := by ring
    have h4 : 1 ≤ Nat.log 2 n + 1 := by omega
    omega

theorem w5bp_of_nc1 (f : (n : ℕ) → (Fin n → Bool) → Bool) (h : InNC1 f) : InW5BP f := by
  obtain ⟨F, c, hFf, hFd⟩ := h
  choose P hPlen hPacc using fun n => exists_prog n (F n)
  refine ⟨P, 4 ^ c, 2 * c, fun n x => by rw [hPacc n x, hFf n x], fun n => ?_⟩
  have hle : (2 : ℕ) ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact le_trans (Nat.pow_log_le_self 2 (by omega)) (by omega)
  have step : (4 : ℕ) ^ (c * (Nat.log 2 n + 1)) ≤ 4 ^ c * (n + 1) ^ (2 * c) := by
    have e1 : (4 : ℕ) ^ (c * (Nat.log 2 n + 1)) = 4 ^ c * 4 ^ (c * Nat.log 2 n) := by
      rw [← pow_add]; ring_nf
    have e2 : (4 : ℕ) ^ (c * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ (2 * c) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]
      ring_nf
    rw [e1, e2]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle (2 * c))
  calc (P n).length ≤ 4 ^ (F n).depth := hPlen n
    _ ≤ 4 ^ (c * (Nat.log 2 n + 1)) := Nat.pow_le_pow_right (by norm_num) (hFd n)
    _ ≤ 4 ^ c * (n + 1) ^ (2 * c) := step

/-- **Barrington's theorem**: a family of Boolean functions is in NC¹ (computed by
Boolean formulas of logarithmic depth) if and only if it is computed by width-5
permutation branching programs of polynomial length. -/
theorem barrington (f : (n : ℕ) → (Fin n → Bool) → Bool) : InNC1 f ↔ InW5BP f :=
  ⟨w5bp_of_nc1 f, nc1_of_w5bp f⟩

/-! ## Sanity checks

These examples confirm that the two classes are inhabited and that the definitions really
do compute the expected Boolean functions. -/

/-- The projection onto the first bit is in NC¹. -/
example : InNC1 (fun n (x : Fin n → Bool) => if h : 0 < n then x ⟨0, h⟩ else false) := by
  refine ⟨fun n => if h : 0 < n then .var ⟨0, h⟩ else .const false, 0, fun n x => ?_, fun n => ?_⟩
  · by_cases h : 0 < n <;> simp [h, Formula.eval]
  · by_cases h : 0 < n <;> simp [h, Formula.depth]

/-- Hence, by Barrington's theorem, it is also computed by polynomial-length width-5
permutation branching programs. -/
example : InW5BP (fun n (x : Fin n → Bool) => if h : 0 < n then x ⟨0, h⟩ else false) := by
  refine (barrington _).mp ?_
  refine ⟨fun n => if h : 0 < n then .var ⟨0, h⟩ else .const false, 0, fun n x => ?_, fun n => ?_⟩
  · by_cases h : 0 < n <;> simp [h, Formula.eval]
  · by_cases h : 0 < n <;> simp [h, Formula.depth]

/-- A concrete width-5 permutation branching program computing the AND of two bits. -/
example : ∃ P : Prog (Fin 2), ∀ x : Fin 2 → Bool, P.accepts x = (x 0 && x 1) := by
  obtain ⟨P, -, hP⟩ := exists_prog 2 (Formula.and (.var 0) (.var 1))
  exact ⟨P, fun x => by rw [hP x]; rfl⟩

end CS

