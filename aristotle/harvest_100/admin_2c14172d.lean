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
## Barrington's theorem

We formalise Barrington's theorem, which identifies `NC¹` (log-depth boolean formulas)
with width-`5` permutation branching programs:

* **Forward direction.** Every boolean formula of depth `d` is computed by a width-`5`
  permutation branching program of length at most `4 ^ d` (in the strong sense of
  `σ`-computation, for an arbitrary `5`-cycle `σ`).
* **Converse direction.** Every width-`5` permutation branching program of length at
  most `2 ^ k` is computed by a boolean formula of depth `O(k)` (explicitly `6 * k + 4`).

Together these say: depth-`d` formulas ↔ length-`4^d` width-`5` programs, i.e.
`NC¹` = width-`5` permutation branching programs.
-/

namespace CS

open Equiv Equiv.Perm

/-! ### Boolean formulas -/

/-- Boolean formulas in `n` variables, over the complete basis `{¬, ∧}` together with
constants.  Depth-`O(log n)` formulas are exactly `NC¹`. -/
inductive Formula (n : ℕ) where
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  deriving DecidableEq

variable {n : ℕ}

/-- The boolean function computed by a formula. -/
def Formula.eval : Formula n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .var i, x => x i
  | .not f, x => !(f.eval x)
  | .and f g, x => (f.eval x) && (g.eval x)

/-- The depth of a formula. -/
def Formula.depth : Formula n → ℕ
  | .const _ => 0
  | .var _ => 0
  | .not f => f.depth + 1
  | .and f g => max f.depth g.depth + 1

/-- Disjunction, as a derived connective. -/
def Formula.or (f g : Formula n) : Formula n := .not (.and (.not f) (.not g))

/-! ### Width-5 permutation branching programs -/

/-- A single instruction of a width-`5` permutation branching program: query a variable,
and apply one of two permutations of the `5` states depending on the answer. -/
abbrev Instr (n : ℕ) := Fin n × Perm (Fin 5) × Perm (Fin 5)

/-- A width-`5` permutation branching program is a list of instructions. -/
abbrev Program (n : ℕ) := List (Instr n)

/-- The permutation applied by a single instruction on a given input. -/
def Instr.eval (I : Instr n) (x : Fin n → Bool) : Perm (Fin 5) :=
  if x I.1 then I.2.1 else I.2.2

/-- The permutation computed by a program on a given input: the ordered product of the
permutations selected by the instructions. -/
def Program.eval (P : Program n) (x : Fin n → Bool) : Perm (Fin 5) :=
  (P.map (fun I => I.eval x)).prod

/-- `P` `σ`-computes the boolean function `f`: the output permutation is `σ` when
`f x = true` and the identity when `f x = false`. -/
def Program.Computes (P : Program n) (σ : Perm (Fin 5)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, P.eval x = if f x then σ else 1

@[simp] theorem Program.eval_nil (x : Fin n → Bool) : Program.eval ([] : Program n) x = 1 := rfl

@[simp] theorem Program.eval_cons (I : Instr n) (P : Program n) (x : Fin n → Bool) :
    Program.eval (I :: P) x = I.eval x * P.eval x := rfl

theorem Program.eval_append (P Q : Program n) (x : Fin n → Bool) :
    (P ++ Q).eval x = P.eval x * Q.eval x := by
  simp [Program.eval, List.prod_append]

/-- Conjugating every instruction of a program by `ρ`. -/
def Program.conj (ρ : Perm (Fin 5)) (P : Program n) : Program n :=
  P.map (fun I => (I.1, ρ * I.2.1 * ρ⁻¹, ρ * I.2.2 * ρ⁻¹))

theorem Program.length_conj (ρ : Perm (Fin 5)) (P : Program n) :
    (P.conj ρ).length = P.length := by simp [Program.conj]

theorem Program.eval_conj (ρ : Perm (Fin 5)) (P : Program n) (x : Fin n → Bool) :
    (P.conj ρ).eval x = ρ * P.eval x * ρ⁻¹ := by
  induction P with
  | nil => simp [Program.conj]
  | cons I P ih =>
      have hc : Program.conj ρ (I :: P)
          = (I.1, ρ * I.2.1 * ρ⁻¹, ρ * I.2.2 * ρ⁻¹) :: Program.conj ρ P := rfl
      rw [hc, Program.eval_cons, ih, Program.eval_cons]
      simp only [Instr.eval]
      split <;> group

theorem Program.Computes.conj {P : Program n} {σ : Perm (Fin 5)}
    {f : (Fin n → Bool) → Bool} (h : P.Computes σ f) (ρ : Perm (Fin 5)) :
    (P.conj ρ).Computes (ρ * σ * ρ⁻¹) f := by
  intro x
  rw [Program.eval_conj, h x]
  split <;> group

/-! ### Five-cycles in `S₅` -/

/-- A permutation of `Fin 5` is a `5`-cycle iff its cycle type is `{5}`. -/
def IsFiveCycle (σ : Perm (Fin 5)) : Prop := σ.cycleType = {5}

theorem isFiveCycle_conj {σ : Perm (Fin 5)} (h : IsFiveCycle σ) (ρ : Perm (Fin 5)) :
    IsFiveCycle (ρ * σ * ρ⁻¹) := by
  unfold IsFiveCycle at *
  rwa [Equiv.Perm.cycleType_conj]

theorem isFiveCycle_inv {σ : Perm (Fin 5)} (h : IsFiveCycle σ) : IsFiveCycle σ⁻¹ := by
  unfold IsFiveCycle at *
  rwa [Equiv.Perm.cycleType_inv]

theorem isConj_of_isFiveCycle {σ τ : Perm (Fin 5)} (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    IsConj σ τ :=
  Equiv.Perm.isConj_iff_cycleType_eq.2 (hσ.trans hτ.symm)

/-- The standard `5`-cycle `0 → 1 → 2 → 3 → 4 → 0`. -/
def c5 : Perm (Fin 5) := finRotate 5

theorem isFiveCycle_c5 : IsFiveCycle c5 := by
  have h := cycleType_finRotate (n := 3)
  simp only [IsFiveCycle, c5]
  exact h

/-- An auxiliary `5`-cycle, conjugate to `c5`, chosen so that the commutator
`[c5, tau0]` is again a `5`-cycle. -/
def tau0 : Perm (Fin 5) := (Equiv.swap 0 1 * Equiv.swap 0 2) * c5 * (Equiv.swap 0 1 * Equiv.swap 0 2)⁻¹

/-- An explicit permutation conjugating `c5` to the commutator `[c5, tau0]`. -/
def pi0 : Perm (Fin 5) := ⟨![0, 4, 1, 3, 2], ![0, 2, 4, 3, 1], by decide, by decide⟩

theorem pi0_conj : pi0 * c5 * pi0⁻¹ = c5 * tau0 * c5⁻¹ * tau0⁻¹ := by
  unfold pi0 c5 tau0
  decide

/-- Every `5`-cycle is a commutator of two `5`-cycles.  This is the group-theoretic heart
of Barrington's theorem. -/
theorem exists_commutator {γ : Perm (Fin 5)} (hγ : IsFiveCycle γ) :
    ∃ σ τ : Perm (Fin 5), IsFiveCycle σ ∧ IsFiveCycle τ ∧ σ * τ * σ⁻¹ * τ⁻¹ = γ := by
  have hτ0 : IsFiveCycle tau0 := isFiveCycle_conj isFiveCycle_c5 _
  have hγ0 : IsFiveCycle (c5 * tau0 * c5⁻¹ * tau0⁻¹) := by
    rw [← pi0_conj]; exact isFiveCycle_conj isFiveCycle_c5 _
  obtain ⟨ρ, hρ⟩ := isConj_iff.1 (isConj_of_isFiveCycle hγ0 hγ)
  refine ⟨ρ * c5 * ρ⁻¹, ρ * tau0 * ρ⁻¹, isFiveCycle_conj isFiveCycle_c5 _,
    isFiveCycle_conj hτ0 _, ?_⟩
  rw [← hρ]; group

/-! ### Forward direction: formulas to programs -/

theorem barrington_forward (i₀ : Fin n) (f : Formula n) :
    ∀ σ : Perm (Fin 5), IsFiveCycle σ →
      ∃ P : Program n, P.length ≤ 4 ^ f.depth ∧ P.Computes σ f.eval := by
  induction f with
  | const b =>
      intro σ _
      cases b with
      | false =>
          refine ⟨[], by simp, ?_⟩
          intro x; simp [Formula.eval]
      | true =>
          refine ⟨[(i₀, σ, σ)], by simp [Formula.depth], ?_⟩
          intro x; simp [Program.eval, Instr.eval, Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[(i, σ, 1)], by simp [Formula.depth], ?_⟩
      intro x; simp [Program.eval, Instr.eval, Formula.eval]
  | not g ih =>
      intro σ hσ
      obtain ⟨P, hlen, hP⟩ := ih σ⁻¹ (isFiveCycle_inv hσ)
      refine ⟨P ++ [(i₀, σ, σ)], ?_, ?_⟩
      · have h1 : 1 ≤ (4 : ℕ) ^ g.depth := Nat.one_le_pow _ _ (by norm_num)
        simp only [Formula.depth, pow_succ, List.length_append, List.length_cons,
          List.length_nil]
        omega
      · intro x
        rw [Program.eval_append, hP x]
        have hI : Program.eval [(i₀, σ, σ)] x = σ := by
          simp [Program.eval, Instr.eval]
        rw [hI]
        cases hg : g.eval x <;> simp [Formula.eval, hg]
  | and g h ihg ihh =>
      intro σ hσ
      obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hcomm⟩ := exists_commutator hσ
      obtain ⟨P₁, hl₁, hP₁⟩ := ihg σ₁ hσ₁
      obtain ⟨P₂, hl₂, hP₂⟩ := ihh σ₂ hσ₂
      obtain ⟨P₃, hl₃, hP₃⟩ := ihg σ₁⁻¹ (isFiveCycle_inv hσ₁)
      obtain ⟨P₄, hl₄, hP₄⟩ := ihh σ₂⁻¹ (isFiveCycle_inv hσ₂)
      refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, ?_, ?_⟩
      · have e1 : (4 : ℕ) ^ g.depth ≤ 4 ^ (max g.depth h.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have e2 : (4 : ℕ) ^ h.depth ≤ 4 ^ (max g.depth h.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        simp only [Formula.depth, pow_succ, List.length_append]
        omega
      · intro x
        rw [Program.eval_append, Program.eval_append, Program.eval_append,
          hP₁ x, hP₂ x, hP₃ x, hP₄ x]
        cases hgx : g.eval x <;> cases hhx : h.eval x <;>
          simp [Formula.eval, hgx, hhx, ← hcomm, mul_assoc]

/-! ### Converse direction: programs to formulas -/

theorem exists_fin5 (p : Fin 5 → Prop) : (∃ m, p m) ↔ p 0 ∨ p 1 ∨ p 2 ∨ p 3 ∨ p 4 := by
  constructor
  · rintro ⟨m, hm⟩; fin_cases m <;> tauto
  · rintro (h | h | h | h | h) <;> exact ⟨_, h⟩

theorem forall_fin5 (p : Fin 5 → Prop) : (∀ m, p m) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 ∧ p 4 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ m; fin_cases m <;> assumption

/-- A balanced `5`-fold disjunction. -/
def or5 (F : Fin 5 → Formula n) : Formula n :=
  .not (.and (.and (.not (F 0)) (.not (F 1)))
             (.and (.and (.not (F 2)) (.not (F 3))) (.not (F 4))))

/-- A balanced `5`-fold conjunction. -/
def and5 (F : Fin 5 → Formula n) : Formula n :=
  .and (.and (F 0) (F 1)) (.and (.and (F 2) (F 3)) (F 4))

theorem or5_depth {F : Fin 5 → Formula n} {D : ℕ} (h : ∀ m, (F m).depth ≤ D) :
    (or5 F).depth ≤ D + 5 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [or5, Formula.depth]
  omega

theorem and5_depth {F : Fin 5 → Formula n} {D : ℕ} (h : ∀ m, (F m).depth ≤ D) :
    (and5 F).depth ≤ D + 3 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [and5, Formula.depth]
  omega

theorem or5_eval (F : Fin 5 → Formula n) (x : Fin n → Bool) :
    ((or5 F).eval x = true) ↔ ∃ m, (F m).eval x = true := by
  rw [exists_fin5]
  simp only [or5, Formula.eval]
  cases h0 : (F 0).eval x <;> cases h1 : (F 1).eval x <;> cases h2 : (F 2).eval x <;>
    cases h3 : (F 3).eval x <;> cases h4 : (F 4).eval x <;> simp_all

theorem and5_eval (F : Fin 5 → Formula n) (x : Fin n → Bool) :
    ((and5 F).eval x = true) ↔ ∀ m, (F m).eval x = true := by
  rw [forall_fin5]
  simp only [and5, Formula.eval, Bool.and_eq_true]
  tauto

/-- Every entry of the permutation computed by a program of length `≤ 2 ^ k` is computed
by a formula of depth `≤ 6 * k + 1`. -/
theorem exists_formula_entry (k : ℕ) : ∀ (P : Program n), P.length ≤ 2 ^ k → ∀ a b : Fin 5,
    ∃ φ : Formula n, φ.depth ≤ 6 * k + 1 ∧ ∀ x, ((φ.eval x = true) ↔ P.eval x a = b) := by
  induction k with
  | zero =>
      intro P hP a b
      match P with
      | [] =>
          refine ⟨.const (decide (a = b)), by simp [Formula.depth], ?_⟩
          intro x; simp [Formula.eval]
      | [(i, p, q)] =>
          have hev : ∀ x : Fin n → Bool,
              Program.eval [((i, p, q) : Instr n)] x a = if x i then p a else q a := by
            intro x
            by_cases hx : x i = true <;>
              simp [Program.eval, Instr.eval, hx]
          by_cases hp : p a = b <;> by_cases hq : q a = b
          · refine ⟨.const true, by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
          · refine ⟨.var i, by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
          · refine ⟨.not (.var i), by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
          · refine ⟨.const false, by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
      | I :: J :: t => simp at hP
  | succ k ih =>
      intro P hP a b
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hpow] at hP
      set m := P.length / 2 with hm
      have hL : (P.take m).length ≤ 2 ^ k := by
        rw [List.length_take]; omega
      have hR : (P.drop m).length ≤ 2 ^ k := by
        rw [List.length_drop]; omega
      obtain ⟨FR, hFRd, hFR⟩ : ∃ F : Fin 5 → Formula n, (∀ j, (F j).depth ≤ 6 * k + 1) ∧
          ∀ j x, (((F j).eval x = true) ↔ Program.eval (P.drop m) x a = j) := by
        choose F h1 h2 using fun j => ih (P.drop m) hR a j
        exact ⟨F, h1, h2⟩
      obtain ⟨FL, hFLd, hFL⟩ : ∃ F : Fin 5 → Formula n, (∀ j, (F j).depth ≤ 6 * k + 1) ∧
          ∀ j x, (((F j).eval x = true) ↔ Program.eval (P.take m) x j = b) := by
        choose F h1 h2 using fun j => ih (P.take m) hL j b
        exact ⟨F, h1, h2⟩
      refine ⟨or5 (fun j => .and (FR j) (FL j)), ?_, ?_⟩
      · have hd : ∀ j, ((Formula.and (FR j) (FL j)).depth) ≤ 6 * k + 2 := by
          intro j
          have h1 := hFRd j
          have h2 := hFLd j
          simp only [Formula.depth]
          omega
        have := or5_depth hd
        omega
      · intro x
        rw [or5_eval]
        have hsplit : P.take m ++ P.drop m = P := List.take_append_drop _ _
        constructor
        · rintro ⟨j, hj⟩
          simp only [Formula.eval, Bool.and_eq_true] at hj
          have h1 := (hFR j x).1 hj.1
          have h2 := (hFL j x).1 hj.2
          rw [← hsplit, Program.eval_append, Equiv.Perm.mul_apply, h1, h2]
        · intro hab
          refine ⟨Program.eval (P.drop m) x a, ?_⟩
          simp only [Formula.eval, Bool.and_eq_true]
          refine ⟨(hFR _ x).2 rfl, (hFL _ x).2 ?_⟩
          rw [← hsplit, Program.eval_append, Equiv.Perm.mul_apply] at hab
          exact hab

theorem barrington_converse (k : ℕ) (P : Program n) (σ : Perm (Fin 5))
    (hP : P.length ≤ 2 ^ k) :
    ∃ ψ : Formula n, ψ.depth ≤ 6 * k + 4 ∧ ∀ x, ((ψ.eval x = true) ↔ P.eval x = σ) := by
  obtain ⟨F, hFd, hF⟩ : ∃ F : Fin 5 → Formula n, (∀ a, (F a).depth ≤ 6 * k + 1) ∧
      ∀ a x, (((F a).eval x = true) ↔ P.eval x a = σ a) := by
    choose F h1 h2 using fun a => exists_formula_entry k P hP a (σ a)
    exact ⟨F, h1, h2⟩
  refine ⟨and5 F, ?_, ?_⟩
  · have := and5_depth hFd
    omega
  · intro x
    rw [and5_eval]
    constructor
    · intro h
      exact Equiv.ext (fun a => (hF a x).1 (h a))
    · intro h a
      exact (hF a x).2 (by rw [h])

/-! ### Barrington's theorem -/

/-- **Barrington's theorem**: `NC¹` equals width-`5` permutation branching programs.

The first component: every depth-`d` boolean formula is `σ`-computed, for any `5`-cycle `σ`,
by a width-`5` permutation branching program of length at most `4 ^ d`.

The second component: conversely, the function decided by any width-`5` permutation
branching program of length at most `2 ^ k` is computed by a boolean formula of depth
at most `6 * k + 4`, i.e. logarithmic in the length of the program.

The forward direction takes a variable index `Fin n` as data: at least one variable must
exist for a nonempty program to be writable (a program over zero variables can only
compute the constant-`false` function). -/
theorem barrington :
    (∀ (n : ℕ) (_i₀ : Fin n) (f : Formula n) (σ : Perm (Fin 5)), IsFiveCycle σ →
        ∃ P : Program n, P.length ≤ 4 ^ f.depth ∧ P.Computes σ f.eval)
    ∧ (∀ (n k : ℕ) (P : Program n) (σ : Perm (Fin 5)), P.length ≤ 2 ^ k →
        ∃ ψ : Formula n, ψ.depth ≤ 6 * k + 4 ∧ ∀ x, ((ψ.eval x = true) ↔ P.eval x = σ)) :=
  ⟨fun _ i₀ f σ hσ => barrington_forward i₀ f σ hσ,
   fun _ k P σ hP => barrington_converse k P σ hP⟩

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

