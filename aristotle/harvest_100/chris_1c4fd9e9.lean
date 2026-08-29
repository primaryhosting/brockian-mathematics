/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires all `import`
-- commands to precede any module docstring.)

import Mathlib

/-!
## Barrington's theorem

We formalise Barrington's theorem, which identifies the class `NC¹` (Boolean formulas of
logarithmic depth) with the class of functions computed by *width-5 permutation branching
programs* of polynomial length.

* `CS.Formula n` are Boolean formulas in the variables `Fin n` built from `¬`, `∧`, `∨`.
  Following the usual convention for Barrington's theorem, `Formula.depth` counts the
  nesting depth of the binary gates (negations are free, since they can be pushed to the
  leaves without changing the depth).
* `CS.BProg n` is a *width-5 permutation branching program*: a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5`, depending on the
  value of that bit.  The value `BProg.eval P x` of the program on the input `x` is the
  product of the permutations selected by the instructions.

The two halves of `CS.barrington` are:

1. every formula of depth `d` is computed by a width-5 permutation branching program of
   length at most `4 ^ d`, with output the prescribed 5-cycle `σ` on accepted inputs and the
   identity on rejected inputs (this is Barrington's construction);
2. conversely, for every width-5 permutation branching program `P` of length `ℓ` and every
   target permutation `σ`, the acceptance predicate `P.eval x = σ` is computed by a formula of
   depth `O(log ℓ)` (a balanced divide-and-conquer evaluation of the product).
-/

namespace CS

open Equiv Equiv.Perm

/-- The group of permutations of five points: the "width 5" of Barrington's theorem. -/
abbrev W : Type := Equiv.Perm (Fin 5)

/-! ### Boolean formulas -/

/-- Boolean formulas over the variables `Fin n`. -/
inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | neg : Formula n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n

/-- The depth of a formula, counting binary gates only (negations are free). -/
def Formula.depth {n : ℕ} : Formula n → ℕ
  | .var _ => 0
  | .neg f => f.depth
  | .conj f g => max f.depth g.depth + 1
  | .disj f g => max f.depth g.depth + 1

/-- The Boolean function computed by a formula. -/
def Formula.eval {n : ℕ} : Formula n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .neg f, x => !f.eval x
  | .conj f g, x => f.eval x && g.eval x
  | .disj f g, x => f.eval x || g.eval x

/-! ### Width-5 permutation branching programs -/

/-- A single instruction of a width-5 permutation branching program: read the input bit
`idx` and output `p₀` or `p₁` according to its value. -/
structure Instr (n : ℕ) where
  idx : Fin n
  p₀ : W
  p₁ : W

/-- A width-5 permutation branching program is a list of instructions. -/
abbrev BProg (n : ℕ) : Type := List (Instr n)

/-- The permutation selected by an instruction on a given input. -/
def Instr.val {n : ℕ} (I : Instr n) (x : Fin n → Bool) : W :=
  if x I.idx then I.p₁ else I.p₀

/-- The value of a branching program: the product of the selected permutations. -/
def BProg.eval {n : ℕ} (P : BProg n) (x : Fin n → Bool) : W :=
  (P.map (fun I => I.val x)).prod

@[simp] theorem BProg.eval_nil {n : ℕ} (x : Fin n → Bool) : ([] : BProg n).eval x = 1 := rfl

@[simp] theorem BProg.eval_cons {n : ℕ} (I : Instr n) (P : BProg n) (x : Fin n → Bool) :
    (I :: P).eval x = I.val x * P.eval x := rfl

theorem BProg.eval_append {n : ℕ} (P Q : BProg n) (x : Fin n → Bool) :
    (P ++ Q).eval x = P.eval x * Q.eval x := by
  simp [BProg.eval]

/-- The reversed program with inverted instructions; it computes the inverse value. -/
def BProg.inv {n : ℕ} (P : BProg n) : BProg n :=
  (P.map (fun I => ⟨I.idx, I.p₀⁻¹, I.p₁⁻¹⟩)).reverse

@[simp] theorem BProg.length_inv {n : ℕ} (P : BProg n) : P.inv.length = P.length := by
  simp [BProg.inv]

theorem BProg.eval_inv {n : ℕ} (P : BProg n) (x : Fin n → Bool) :
    P.inv.eval x = (P.eval x)⁻¹ := by
  induction P with
  | nil => simp [BProg.inv]
  | cons I P ih =>
      have : (I :: P).inv = P.inv ++ [⟨I.idx, I.p₀⁻¹, I.p₁⁻¹⟩] := by
        simp [BProg.inv]
      rw [this, BProg.eval_append, ih]
      simp [BProg.eval, Instr.val]
      cases x I.idx <;> simp [mul_comm]

/-- Conjugating all instructions of a program by `θ`. -/
def BProg.conj {n : ℕ} (θ : W) (P : BProg n) : BProg n :=
  P.map (fun I => ⟨I.idx, θ * I.p₀ * θ⁻¹, θ * I.p₁ * θ⁻¹⟩)

@[simp] theorem BProg.length_conj {n : ℕ} (θ : W) (P : BProg n) :
    (P.conj θ).length = P.length := by
  simp [BProg.conj]

theorem BProg.eval_conj {n : ℕ} (θ : W) (P : BProg n) (x : Fin n → Bool) :
    (P.conj θ).eval x = θ * P.eval x * θ⁻¹ := by
  induction P with
  | nil => simp [BProg.conj]
  | cons I P ih =>
      have : (I :: P).conj θ = (⟨I.idx, θ * I.p₀ * θ⁻¹, θ * I.p₁ * θ⁻¹⟩ : Instr n) :: P.conj θ :=
        rfl
      rw [this, BProg.eval_cons, ih]
      have : (Instr.val ⟨I.idx, θ * I.p₀ * θ⁻¹, θ * I.p₁ * θ⁻¹⟩ x) = θ * I.val x * θ⁻¹ := by
        simp only [Instr.val]
        cases x I.idx <;> simp
      rw [this]
      group

/-- Multiplying the value of a (nonempty) program on the left by a constant, by modifying
its first instruction. -/
def BProg.lmul {n : ℕ} (g : W) : BProg n → BProg n
  | [] => []
  | I :: P => ⟨I.idx, g * I.p₀, g * I.p₁⟩ :: P

@[simp] theorem BProg.length_lmul {n : ℕ} (g : W) (P : BProg n) :
    (BProg.lmul g P).length = P.length := by
  cases P <;> simp [BProg.lmul]

theorem BProg.lmul_ne_nil {n : ℕ} (g : W) {P : BProg n} (h : P ≠ []) :
    BProg.lmul g P ≠ [] := by
  cases P with
  | nil => exact absurd rfl h
  | cons I P => simp [BProg.lmul]

theorem BProg.eval_lmul {n : ℕ} (g : W) {P : BProg n} (h : P ≠ []) (x : Fin n → Bool) :
    (BProg.lmul g P).eval x = g * P.eval x := by
  cases P with
  | nil => exact absurd rfl h
  | cons I P =>
      show (Instr.val ⟨I.idx, g * I.p₀, g * I.p₁⟩ x) * P.eval x = g * (I.val x * P.eval x)
      have : (Instr.val ⟨I.idx, g * I.p₀, g * I.p₁⟩ x) = g * I.val x := by
        simp only [Instr.val]
        cases x I.idx <;> simp
      rw [this, mul_assoc]

/-! ### The commutator trick -/

/-- The value of the commutator program `P Q P⁻¹ Q⁻¹`. -/
theorem comm_prog {n : ℕ} {P Q : BProg n} {σ τ : W} {f g : (Fin n → Bool) → Bool}
    (hP : ∀ x, P.eval x = if f x then σ else 1)
    (hQ : ∀ x, Q.eval x = if g x then τ else 1) (x : Fin n → Bool) :
    (P ++ Q ++ P.inv ++ Q.inv).eval x = if (f x && g x) then σ * τ * σ⁻¹ * τ⁻¹ else 1 := by
  rw [BProg.eval_append, BProg.eval_append, BProg.eval_append, BProg.eval_inv, BProg.eval_inv,
    hP, hQ]
  cases hf : f x <;> cases hg : g x <;> simp

/-! ### Barrington's construction (formulas → branching programs) -/

/-- The concrete 5-cycle `(0 1 2 3 4)`. -/
def sigma0 : W := List.formPerm [0, 1, 2, 3, 4]

/-- The concrete 5-cycle `(0 3 1 2 4)`. -/
def tau0 : W := List.formPerm [0, 3, 1, 2, 4]

theorem cycleType_formPerm_of_length_five (l : List (Fin 5)) (hnd : l.Nodup)
    (hl : l.length = 5) : (List.formPerm l).cycleType = {5} := by
  have hcyc : (List.formPerm l).IsCycle := List.isCycle_formPerm hnd (by omega)
  have hsupp : (List.formPerm l).support = l.toFinset :=
    List.support_formPerm_of_nodup l hnd (by
      intro x hx
      rw [hx] at hl
      simp at hl)
  rw [hcyc.cycleType, hsupp, List.toFinset_card_of_nodup hnd, hl]

theorem sigma0_cycleType : sigma0.cycleType = {5} := by
  apply cycleType_formPerm_of_length_five <;> decide

theorem tau0_cycleType : tau0.cycleType = {5} := by
  apply cycleType_formPerm_of_length_five <;> decide

theorem comm_cycleType : (sigma0 * tau0 * sigma0⁻¹ * tau0⁻¹).cycleType = {5} := by
  have h : sigma0 * tau0 * sigma0⁻¹ * tau0⁻¹ = List.formPerm [0, 2, 4, 3, 1] := by
    simp only [sigma0, tau0]
    decide
  rw [h]
  apply cycleType_formPerm_of_length_five <;> decide

/-- Relabelling: a program with output `γ` can be turned into one with output any conjugate
`γ'`, without changing its length. -/
theorem relabel {n : ℕ} {P : BProg n} {γ γ' : W} {f : (Fin n → Bool) → Bool}
    (h : ∀ x, P.eval x = if f x then γ else 1) (hc : IsConj γ γ') :
    ∃ P' : BProg n, P'.length = P.length ∧ (P ≠ [] → P' ≠ []) ∧
      ∀ x, P'.eval x = if f x then γ' else 1 := by
  rw [isConj_iff] at hc
  obtain ⟨θ, hθ⟩ := hc
  refine ⟨P.conj θ, by simp, ?_, ?_⟩
  · intro hne
    simpa [BProg.conj] using hne
  · intro x
    rw [BProg.eval_conj, h]
    cases f x <;> simp [hθ]

/-- **Barrington's construction.** Every formula of depth `d` is computed, with output any
prescribed 5-cycle `σ`, by a nonempty width-5 permutation branching program of length at
most `4 ^ d`. -/
theorem exists_prog {n : ℕ} (F : Formula n) :
    ∀ σ : W, σ.cycleType = {5} →
      ∃ P : BProg n, P ≠ [] ∧ P.length ≤ 4 ^ F.depth ∧
        ∀ x, P.eval x = if F.eval x then σ else 1 := by
  induction F with
  | var i =>
      intro σ _
      refine ⟨[⟨i, 1, σ⟩], by simp, by simp [Formula.depth], ?_⟩
      intro x
      simp only [BProg.eval_cons, BProg.eval_nil, mul_one, Instr.val, Formula.eval]
      cases x i <;> simp
  | neg F ih =>
      intro σ hσ
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ih σ⁻¹ (by rw [cycleType_inv]; exact hσ)
      refine ⟨BProg.lmul σ Q, BProg.lmul_ne_nil σ hQne, by simpa [Formula.depth] using hQlen, ?_⟩
      intro x
      rw [BProg.eval_lmul σ hQne, hQ]
      simp only [Formula.eval]
      cases F.eval x <;> simp
  | conj F G ihF ihG =>
      intro σ hσ
      obtain ⟨P, hPne, hPlen, hP⟩ := ihF sigma0 sigma0_cycleType
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ihG tau0 tau0_cycleType
      have key := comm_prog hP hQ
      obtain ⟨R, hRlen, hRne, hR⟩ :=
        relabel key (isConj_iff_cycleType_eq.2 (by rw [comm_cycleType, hσ]))
      refine ⟨R, hRne (by simp [hPne]), ?_, hR⟩
      rw [hRlen]
      have h1 : P.length ≤ 4 ^ (max F.depth G.depth) :=
        hPlen.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : Q.length ≤ 4 ^ (max F.depth G.depth) :=
        hQlen.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : (P ++ Q ++ P.inv ++ Q.inv).length = 2 * (P.length + Q.length) := by
        simp [BProg.length_inv]; ring
      rw [this]
      show 2 * (P.length + Q.length) ≤ 4 ^ (max F.depth G.depth + 1)
      rw [pow_succ]
      omega
  | disj F G ihF ihG =>
      intro σ hσ
      -- programs for the negations
      obtain ⟨P0, hP0ne, hP0len, hP0⟩ := ihF sigma0⁻¹ (by rw [cycleType_inv]; exact sigma0_cycleType)
      obtain ⟨Q0, hQ0ne, hQ0len, hQ0⟩ := ihG tau0⁻¹ (by rw [cycleType_inv]; exact tau0_cycleType)
      set P := BProg.lmul sigma0 P0 with hPdef
      set Q := BProg.lmul tau0 Q0 with hQdef
      have hPne : P ≠ [] := BProg.lmul_ne_nil _ hP0ne
      have hQne : Q ≠ [] := BProg.lmul_ne_nil _ hQ0ne
      have hP : ∀ x, P.eval x = if (!F.eval x) then sigma0 else 1 := by
        intro x
        rw [hPdef, BProg.eval_lmul sigma0 hP0ne, hP0]
        cases F.eval x <;> simp
      have hQ : ∀ x, Q.eval x = if (!G.eval x) then tau0 else 1 := by
        intro x
        rw [hQdef, BProg.eval_lmul tau0 hQ0ne, hQ0]
        cases G.eval x <;> simp
      have key := comm_prog hP hQ
      obtain ⟨R, hRlen, hRne, hR⟩ :=
        relabel key (isConj_iff_cycleType_eq.2
          (by rw [comm_cycleType, cycleType_inv]; exact hσ.symm))
      have hRne' : R ≠ [] := hRne (by simp [hPne])
      refine ⟨BProg.lmul σ R, BProg.lmul_ne_nil σ hRne', ?_, ?_⟩
      · rw [BProg.length_lmul, hRlen]
        have h1 : P.length ≤ 4 ^ (max F.depth G.depth) := by
          rw [hPdef, BProg.length_lmul]
          exact hP0len.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
        have h2 : Q.length ≤ 4 ^ (max F.depth G.depth) := by
          rw [hQdef, BProg.length_lmul]
          exact hQ0len.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        have : (P ++ Q ++ P.inv ++ Q.inv).length = 2 * (P.length + Q.length) := by
          simp [BProg.length_inv]; ring
        rw [this]
        show 2 * (P.length + Q.length) ≤ 4 ^ (max F.depth G.depth + 1)
        rw [pow_succ]
        omega
      · intro x
        rw [BProg.eval_lmul σ hRne', hR]
        simp only [Formula.eval]
        cases F.eval x <;> cases G.eval x <;> simp

/-! ### The converse: evaluating a branching program by a shallow formula -/

/-- The constantly false formula (of depth 1). -/
def Formula.falseF {n : ℕ} (i : Fin n) : Formula n := .conj (.var i) (.neg (.var i))

/-- The constantly true formula (of depth 1). -/
def Formula.trueF {n : ℕ} (i : Fin n) : Formula n := .disj (.var i) (.neg (.var i))

/-- A constant formula of depth 1. -/
def Formula.constF {n : ℕ} (i : Fin n) (b : Bool) : Formula n :=
  if b then Formula.trueF i else Formula.falseF i

@[simp] theorem Formula.depth_constF {n : ℕ} (i : Fin n) (b : Bool) :
    (Formula.constF i b).depth = 1 := by
  cases b <;> simp [Formula.constF, Formula.trueF, Formula.falseF, Formula.depth]

@[simp] theorem Formula.eval_constF {n : ℕ} (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    (Formula.constF i b).eval x = b := by
  cases b <;> simp [Formula.constF, Formula.trueF, Formula.falseF, Formula.eval] <;>
    cases x i <;> simp

/-- The disjunction of a list of formulas. -/
def Formula.orList {n : ℕ} (i : Fin n) (l : List (Formula n)) : Formula n :=
  l.foldr Formula.disj (Formula.falseF i)

theorem Formula.eval_orList {n : ℕ} (i : Fin n) (l : List (Formula n)) (x : Fin n → Bool) :
    (Formula.orList i l).eval x = l.any (fun f => f.eval x) := by
  induction l with
  | nil =>
      simp only [Formula.orList, List.foldr_nil, List.any_nil]
      simp [Formula.falseF, Formula.eval]
  | cons f l ih =>
      simp only [Formula.orList, List.foldr_cons, List.any_cons] at *
      simp [Formula.eval, ih]

theorem Formula.depth_orList {n : ℕ} (i : Fin n) (l : List (Formula n)) {d : ℕ}
    (hd : ∀ f ∈ l, f.depth ≤ d) (h1 : 1 ≤ d) :
    (Formula.orList i l).depth ≤ d + l.length := by
  induction l with
  | nil => simpa [Formula.orList, Formula.falseF, Formula.depth] using h1
  | cons f l ih =>
      have hf : f.depth ≤ d := hd f (by simp)
      have hrest : (Formula.orList i l).depth ≤ d + l.length :=
        ih (fun g hg => hd g (by simp [hg]))
      simp only [Formula.orList, List.foldr_cons] at *
      simp only [Formula.depth, List.length_cons]
      omega

/-- Every width-5 permutation branching program of length `ℓ` has its acceptance predicate
computed by a formula of depth at most `121 * ⌈log₂ ℓ⌉ + 1`. -/
theorem exists_formula {n : ℕ} (i : Fin n) :
    ∀ (N : ℕ) (P : BProg n), P.length ≤ N →
      ∃ φ : W → Formula n, (∀ g, (φ g).depth ≤ 121 * Nat.clog 2 P.length + 1) ∧
        (∀ g x, (φ g).eval x = decide (P.eval x = g)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro P hPN
    match P with
    | [] =>
        refine ⟨fun g => Formula.constF i (decide ((1 : W) = g)), by simp, ?_⟩
        intro g x
        simp
    | [I] =>
        refine ⟨fun g =>
          if I.p₀ = g then (if I.p₁ = g then Formula.trueF i else Formula.neg (.var I.idx))
          else (if I.p₁ = g then Formula.var I.idx else Formula.falseF i), ?_, ?_⟩
        · intro g
          by_cases h0 : I.p₀ = g <;> by_cases h1 : I.p₁ = g <;>
            simp [h0, h1, Formula.trueF, Formula.falseF, Formula.depth]
        · intro g x
          have hev : (([I] : BProg n)).eval x = if x I.idx then I.p₁ else I.p₀ := by
            simp [BProg.eval, Instr.val]
          rw [hev]
          by_cases h0 : I.p₀ = g <;> by_cases h1 : I.p₁ = g <;>
            simp [h0, h1, Formula.trueF, Formula.falseF, Formula.eval] <;>
            cases hx : x I.idx <;> simp_all
    | I :: J :: P'' =>
      set Q : BProg n := I :: J :: P'' with hQdef
      have hlen2 : 2 ≤ Q.length := by simp [hQdef]
      set k := Q.length / 2 with hk
      have hk1 : 1 ≤ k := by omega
      have hk2 : k < Q.length := by omega
      have hlen1 : (Q.take k).length = k := by
        rw [List.length_take]; omega
      have hlen3 : (Q.drop k).length = Q.length - k := by
        rw [List.length_drop]
      obtain ⟨φ1, hd1, he1⟩ := IH (Q.length - 1) (by omega) (Q.take k) (by omega)
      obtain ⟨φ2, hd2, he2⟩ := IH (Q.length - 1) (by omega) (Q.drop k) (by omega)
      -- the bound
      have hclog : Nat.clog 2 (Q.length - k) + 1 = Nat.clog 2 Q.length := by
        rw [Nat.clog_of_two_le (by norm_num) hlen2]
        congr 1
        congr 1
        omega
      have hmono : Nat.clog 2 (Q.take k).length ≤ Nat.clog 2 (Q.drop k).length := by
        rw [hlen1, hlen3]
        exact Nat.clog_mono_right _ (by omega)
      set D := 121 * Nat.clog 2 (Q.drop k).length + 1 with hD
      refine ⟨fun g => Formula.orList i
        ((Finset.univ : Finset W).toList.map (fun a => Formula.conj (φ1 a) (φ2 (a⁻¹ * g)))), ?_, ?_⟩
      · intro g
        have hcard : ((Finset.univ : Finset W).toList.map
            (fun a => Formula.conj (φ1 a) (φ2 (a⁻¹ * g)))).length = 120 := by
          rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin]
          rfl
        have hbnd : ∀ f ∈ ((Finset.univ : Finset W).toList.map
            (fun a => Formula.conj (φ1 a) (φ2 (a⁻¹ * g)))), f.depth ≤ D + 1 := by
          intro f hf
          rw [List.mem_map] at hf
          obtain ⟨a, _, rfl⟩ := hf
          have b1 : (φ1 a).depth ≤ D := by
            refine (hd1 a).trans ?_
            rw [hD]
            have := hmono
            omega
          have b2 : (φ2 (a⁻¹ * g)).depth ≤ D := hd2 _
          simp only [Formula.depth]
          omega
        have := Formula.depth_orList i _ hbnd (by omega)
        rw [hcard] at this
        refine this.trans ?_
        rw [hD, hlen3]
        omega
      · intro g x
        rw [Formula.eval_orList]
        have hsplit : Q.eval x = (Q.take k).eval x * (Q.drop k).eval x := by
          rw [← BProg.eval_append, List.take_append_drop]
        rw [hsplit]
        simp only [List.any_map, List.any_eq_true, Finset.mem_toList, Finset.mem_univ,
          Function.comp_apply, true_and, Formula.eval, he1, he2, Bool.and_eq_true,
          decide_eq_true_eq]
        by_cases hgoal : (Q.take k).eval x * (Q.drop k).eval x = g
        · simp only [hgoal, decide_true, eq_iff_iff, iff_true]
          exact ⟨(Q.take k).eval x, rfl, by rw [← hgoal]; group⟩
        · simp only [hgoal, decide_false, eq_iff_iff, iff_false, not_exists]
          rintro a ⟨rfl, h2⟩
          rw [h2] at hgoal
          exact hgoal (by group)

/-! ### Barrington's theorem -/

/-- **Barrington's theorem**: `NC¹` equals width-5 permutation branching programs.

The first component is the hard direction: any Boolean formula of depth `d` (with negations
free, i.e. `d` is the nesting depth of the binary gates) is computed by a width-5 permutation
branching program of length at most `4 ^ d`, whose output is a prescribed 5-cycle `σ` on
accepted inputs and the identity on rejected inputs.  In particular formulas of depth
`O(log n)` — i.e. functions in `NC¹` — are computed by width-5 permutation branching programs
of polynomial length.

The second component is the converse: the acceptance predicate `P.eval x = σ` of a width-5
permutation branching program of length `ℓ` is computed by a Boolean formula of depth at most
`121 * ⌈log₂ ℓ⌉ + 1`, so a polynomial-length program yields a logarithmic-depth formula. -/
theorem barrington {n : ℕ} (hn : 0 < n) :
    (∀ (F : Formula n) (σ : W), σ.cycleType = {5} →
        ∃ P : BProg n, P.length ≤ 4 ^ F.depth ∧
          ∀ x, P.eval x = if F.eval x then σ else 1) ∧
    (∀ (P : BProg n) (σ : W), ∃ F : Formula n,
        F.depth ≤ 121 * Nat.clog 2 P.length + 1 ∧
          ∀ x, F.eval x = decide (P.eval x = σ)) := by
  constructor
  · intro F σ hσ
    obtain ⟨P, _, hlen, hP⟩ := exists_prog F σ hσ
    exact ⟨P, hlen, hP⟩
  · intro P σ
    obtain ⟨φ, hd, he⟩ := exists_formula ⟨0, hn⟩ P.length P le_rfl
    exact ⟨φ σ, hd σ, fun x => he σ x⟩

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

