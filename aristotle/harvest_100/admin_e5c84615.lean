import Mathlib

/-!
# Basic definitions for Barrington's theorem

* Boolean formulas over the basis `{¬, ∧, ∨}` (with constants), together with their
  depth and semantics.  Non-uniform `NC¹` is the class of families of boolean functions
  computed by formulas of logarithmic depth.
* Width-5 permutation branching programs: a program is a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5` (or is a
  constant instruction).  The value of the program is the product of the permutations
  produced by its instructions, and the program accepts iff this product lies in a
  designated set of accepting permutations.
-/

namespace CS

open Equiv Equiv.Perm

/-- Permutations of a five element set. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A permutation of `Fin 5` is a five-cycle if it is a cycle whose support is everything. -/
def IsFiveCycle (σ : Perm5) : Prop := σ.IsCycle ∧ σ.support.card = 5

theorem IsFiveCycle.ne_one {σ : Perm5} (h : IsFiveCycle σ) : σ ≠ 1 := h.1.ne_one

theorem IsFiveCycle.inv {σ : Perm5} (h : IsFiveCycle σ) : IsFiveCycle σ⁻¹ :=
  ⟨h.1.inv, by rw [Equiv.Perm.support_inv]; exact h.2⟩

theorem IsFiveCycle.conj {σ : Perm5} (h : IsFiveCycle σ) (τ : Perm5) :
    IsFiveCycle (τ * σ * τ⁻¹) := by
  refine ⟨h.1.conj, ?_⟩
  rw [Equiv.Perm.support_conj]
  simpa using h.2

theorem IsFiveCycle.cycleType {σ : Perm5} (h : IsFiveCycle σ) : σ.cycleType = {5} := by
  rw [h.1.cycleType, h.2]

/-- Any two five-cycles in `S₅` are conjugate. -/
theorem IsFiveCycle.exists_conj {σ τ : Perm5} (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    ∃ ρ : Perm5, ρ * σ * ρ⁻¹ = τ := by
  have h : IsConj σ τ := Equiv.Perm.isConj_iff_cycleType_eq.2 (by rw [hσ.cycleType, hτ.cycleType])
  exact isConj_iff.1 h

theorem isFiveCycle_formPerm (l : List (Fin 5)) (hl : l.Nodup) (h5 : l.length = 5) :
    IsFiveCycle l.formPerm := by
  refine ⟨List.isCycle_formPerm hl (by omega), ?_⟩
  rw [List.support_formPerm_of_nodup l hl (by rintro x rfl; simp at h5)]
  rw [List.toFinset_card_of_nodup hl, h5]

/-- Boolean formulas in `n` variables over the basis `{¬, ∧, ∨}` with constants. -/
inductive Formula (n : ℕ) : Type
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

/-- The boolean function computed by a formula. -/
def Formula.eval {n : ℕ} : Formula n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .var i, x => x i
  | .not p, x => !(p.eval x)
  | .and p q, x => p.eval x && q.eval x
  | .or p q, x => p.eval x || q.eval x

/-- The depth of a formula (variables and constants have depth `0`). -/
def Formula.depth {n : ℕ} : Formula n → ℕ
  | .const _ => 0
  | .var _ => 0
  | .not p => p.depth + 1
  | .and p q => max p.depth q.depth + 1
  | .or p q => max p.depth q.depth + 1

/-- The big disjunction of a list of formulas. -/
def Formula.orList {n : ℕ} : List (Formula n) → Formula n
  | [] => .const false
  | p :: t => .or p (orList t)

@[simp] theorem Formula.eval_orList {n : ℕ} (L : List (Formula n)) (x : Fin n → Bool) :
    (Formula.orList L).eval x = L.any (fun p => p.eval x) := by
  induction L with
  | nil => simp [Formula.orList, Formula.eval]
  | cons p t ih => simp [Formula.orList, Formula.eval, ih]

theorem Formula.depth_orList {n : ℕ} (L : List (Formula n)) (D : ℕ)
    (h : ∀ p ∈ L, p.depth ≤ D) : (Formula.orList L).depth ≤ D + L.length := by
  induction L with
  | nil => simp [Formula.orList, Formula.depth]
  | cons p t ih =>
      have h1 : p.depth ≤ D := h p (by simp)
      have h2 := ih (fun q hq => h q (by simp [hq]))
      simp only [Formula.orList, Formula.depth, List.length_cons]
      omega

/-- An instruction of a width-5 permutation branching program: either it reads the input
bit `i` and produces `p` or `q` accordingly, or it produces a fixed permutation. -/
inductive Instr (n : ℕ) : Type
  | test : Fin n → Perm5 → Perm5 → Instr n
  | const : Perm5 → Instr n

/-- The permutation produced by an instruction on a given input. -/
def Instr.run {n : ℕ} : Instr n → (Fin n → Bool) → Perm5
  | .test i p q, x => if x i then p else q
  | .const p, _ => p

/-- The value of a width-5 permutation branching program: the product, in order, of the
permutations produced by its instructions. -/
def BPeval {n : ℕ} (P : List (Instr n)) (x : Fin n → Bool) : Perm5 :=
  (P.map (fun I => I.run x)).prod

@[simp] theorem BPeval_nil {n : ℕ} (x : Fin n → Bool) : BPeval ([] : List (Instr n)) x = 1 := rfl

@[simp] theorem BPeval_cons {n : ℕ} (I : Instr n) (P : List (Instr n)) (x : Fin n → Bool) :
    BPeval (I :: P) x = I.run x * BPeval P x := rfl

@[simp] theorem BPeval_append {n : ℕ} (P Q : List (Instr n)) (x : Fin n → Bool) :
    BPeval (P ++ Q) x = BPeval P x * BPeval Q x := by
  simp [BPeval]

/-- `P` computes `f` in Barrington normal form with respect to the permutation `σ`: the
program outputs `σ` on inputs accepted by `f` and the identity on the others. -/
def Computes {n : ℕ} (P : List (Instr n)) (σ : Perm5) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, BPeval P x = if f x then σ else 1

/-- Non-uniform `NC¹`: families of boolean functions computed by formulas of depth
`O(log n)` (equivalently, by boolean circuits of fan-in two and logarithmic depth). -/
def InNC1 (f : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ (c : ℕ) (φ : (n : ℕ) → Formula n), ∀ n : ℕ,
    (∀ x, (φ n).eval x = f n x) ∧ (φ n).depth ≤ c * (Nat.log 2 (n + 1) + 1)

/-- A program is in the standard model if each of its instructions reads an input bit
(constant instructions are a convenience used in intermediate constructions only). -/
def ConstFree {n : ℕ} (P : List (Instr n)) : Prop := ∀ I ∈ P, ∀ p : Perm5, I ≠ .const p

/-- Families of boolean functions computed by polynomial-length width-5 permutation
branching programs, with an arbitrary set of accepting permutations. -/
def InW5BP (f : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ (c : ℕ) (A : ℕ → Finset Perm5) (P : (n : ℕ) → List (Instr n)), ∀ n : ℕ,
    (P n).length ≤ c * (n + 1) ^ c ∧ ConstFree (P n) ∧
      ∀ x, (f n x = true ↔ BPeval (P n) x ∈ A n)

end CS

import RequestProject.Basic

/-!
# Barrington's theorem, the easy direction

A width-5 permutation branching program of length `ℓ` is simulated by a boolean formula of
depth `O(log ℓ)`: one computes, by divide and conquer, for each permutation `π` the boolean
predicate "the product of the instructions over this block equals `π`".
-/

namespace CS

open Equiv Equiv.Perm

/-- The number of permutations of a five element set. -/
def K5 : ℕ := Fintype.card Perm5

theorem length_univ_toList : (Finset.univ : Finset Perm5).toList.length = K5 := by
  rw [Finset.length_toList, Finset.card_univ, K5]

theorem card_le_K5 (A : Finset Perm5) : A.toList.length ≤ K5 := by
  rw [Finset.length_toList, K5, ← Finset.card_univ]
  exact Finset.card_le_univ A

/-- Divide and conquer: for every block of instructions and every permutation `π` there is
a formula of depth `O(log ℓ)` deciding whether the product of the block equals `π`. -/
theorem exists_formula_eq (n : ℕ) : ∀ (ℓ : ℕ) (P : List (Instr n)), P.length = ℓ →
    ∀ π : Perm5, ∃ φ : Formula n, (∀ x, (φ.eval x = true ↔ BPeval P x = π)) ∧
      φ.depth ≤ (K5 + 1) * Nat.clog 2 ℓ + 1 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ IH =>
    intro P hP π
    match hℓ : ℓ with
    | 0 =>
        subst hℓ
        have hPnil : P = [] := List.length_eq_zero_iff.1 hP
        subst hPnil
        refine ⟨.const (decide ((1 : Perm5) = π)), ?_, by simp [Formula.depth]⟩
        intro x; simp [Formula.eval]
    | 1 =>
        subst hℓ
        obtain ⟨I, rfl⟩ := List.length_eq_one_iff.1 hP
        have hval : ∀ x : Fin n → Bool, BPeval [I] x = I.run x := by
          intro x; simp [BPeval]
        match I with
        | .const p =>
            refine ⟨.const (decide (p = π)), ?_, by simp [Formula.depth]⟩
            intro x; simp [Formula.eval, hval, Instr.run]
        | .test i p q =>
            by_cases hp : p = π <;> by_cases hq : q = π
            · refine ⟨.const true, ?_, by simp [Formula.depth]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, Instr.run, hx, hp, hq]
            · refine ⟨.var i, ?_, by simp [Formula.depth, Nat.clog]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, Instr.run, hx, hp, hq]
            · refine ⟨.not (.var i), ?_, by simp [Formula.depth, Nat.clog]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, Instr.run, hx, hp, hq]
            · refine ⟨.const false, ?_, by simp [Formula.depth]⟩
              intro x
              by_cases hx : x i <;> simp [Formula.eval, hval, Instr.run, hx, hp, hq]
    | (k + 2) =>
        subst hℓ
        set ℓ := k + 2 with hℓdef
        set m := (ℓ + 1) / 2 with hm
        have hm1 : 1 ≤ m := by omega
        have hmℓ : m < ℓ := by omega
        have hsub : ℓ - m ≤ m := by omega
        have hsubℓ : ℓ - m < ℓ := by omega
        set A := P.take m with hA
        set B := P.drop m with hB
        have hlenA : A.length = m := by rw [hA, List.length_take, hP]; omega
        have hlenB : B.length = ℓ - m := by rw [hB, List.length_drop, hP]
        have hsplit : ∀ x : Fin n → Bool, BPeval P x = BPeval A x * BPeval B x := by
          intro x
          conv_lhs => rw [← List.take_append_drop m P]
          rw [BPeval_append]
        choose φA hφA hdA using fun ρ => IH m hmℓ A hlenA ρ
        choose φB hφB hdB using fun ρ => IH (ℓ - m) hsubℓ B hlenB ρ
        refine ⟨Formula.orList ((Finset.univ : Finset Perm5).toList.map
          (fun ρ => .and (φA ρ) (φB (ρ⁻¹ * π)))), ?_, ?_⟩
        · intro x
          rw [Formula.eval_orList]
          simp only [List.any_map, List.any_eq_true, Function.comp_def, Finset.mem_toList,
            Finset.mem_univ, true_and, Formula.eval, Bool.and_eq_true]
          constructor
          · rintro ⟨ρ, h1, h2⟩
            rw [hsplit x, (hφA ρ x).1 h1, (hφB (ρ⁻¹ * π) x).1 h2]
            group
          · intro h
            refine ⟨BPeval A x, (hφA _ x).2 rfl, (hφB _ x).2 ?_⟩
            rw [hsplit x] at h
            rw [← h]
            group
        · have hdepth : ∀ p ∈ ((Finset.univ : Finset Perm5).toList.map
              (fun ρ => (Formula.and (φA ρ) (φB (ρ⁻¹ * π)) : Formula n))),
              p.depth ≤ (K5 + 1) * Nat.clog 2 m + 2 := by
            intro p hp
            simp only [List.mem_map, Finset.mem_toList] at hp
            obtain ⟨ρ, -, rfl⟩ := hp
            have h1 := hdA ρ
            have h2 : (φB (ρ⁻¹ * π)).depth ≤ (K5 + 1) * Nat.clog 2 m + 1 := by
              refine le_trans (hdB (ρ⁻¹ * π)) ?_
              have := Nat.clog_mono_right 2 hsub
              have := Nat.mul_le_mul_left (K5 + 1) this
              omega
            simp only [Formula.depth]
            omega
          have hor := Formula.depth_orList _ _ hdepth
          rw [List.length_map, length_univ_toList] at hor
          have hclog : Nat.clog 2 ℓ = Nat.clog 2 m + 1 := by
            rw [Nat.clog_of_two_le (by norm_num) (by omega)]
            congr 1
          rw [hclog]
          have : (K5 + 1) * (Nat.clog 2 m + 1) = (K5 + 1) * Nat.clog 2 m + K5 + 1 := by ring
          omega

/-- A width-5 permutation branching program with an arbitrary set of accepting
permutations is simulated by a formula of depth `O(log ℓ)`. -/
theorem exists_formula_of_bp {n : ℕ} (P : List (Instr n)) (A : Finset Perm5) :
    ∃ φ : Formula n, (∀ x, (φ.eval x = true ↔ BPeval P x ∈ A)) ∧
      φ.depth ≤ (K5 + 1) * Nat.clog 2 P.length + 1 + K5 := by
  choose φ hφ hd using fun π => exists_formula_eq n P.length P rfl π
  refine ⟨Formula.orList (A.toList.map φ), ?_, ?_⟩
  · intro x
    rw [Formula.eval_orList]
    simp only [List.any_map, List.any_eq_true, Function.comp_def, Finset.mem_toList]
    constructor
    · rintro ⟨π, hπ, h⟩
      rw [(hφ π x).1 h]; exact hπ
    · intro h
      exact ⟨BPeval P x, h, (hφ _ x).2 rfl⟩
  · have hor := Formula.depth_orList (A.toList.map φ) ((K5 + 1) * Nat.clog 2 P.length + 1)
      (by
        intro p hp
        simp only [List.mem_map, Finset.mem_toList] at hp
        obtain ⟨π, -, rfl⟩ := hp
        exact hd π)
    rw [List.length_map] at hor
    have := card_le_K5 A
    omega

end CS

import RequestProject.Basic

/-!
# Barrington's theorem, the hard direction

Every boolean formula of depth `d` is computed, in Barrington normal form with respect to
any prescribed five-cycle, by a width-5 permutation branching program of length at most
`4 ^ d`.
-/

namespace CS

open Equiv Equiv.Perm

/-! ### A commutator of five-cycles which is again a five-cycle -/

/-- A distinguished five-cycle. -/
def alpha0 : Perm5 := ([0, 1, 2, 3, 4] : List (Fin 5)).formPerm

/-- A second distinguished five-cycle, whose commutator with `alpha0` is a five-cycle. -/
def beta0 : Perm5 := ([0, 3, 4, 1, 2] : List (Fin 5)).formPerm

/-- The commutator `⁅alpha0, beta0⁆`. -/
def sigma0 : Perm5 := ([0, 3, 2, 4, 1] : List (Fin 5)).formPerm

theorem isFiveCycle_alpha0 : IsFiveCycle alpha0 :=
  isFiveCycle_formPerm _ (by decide) (by decide)

theorem isFiveCycle_beta0 : IsFiveCycle beta0 :=
  isFiveCycle_formPerm _ (by decide) (by decide)

theorem isFiveCycle_sigma0 : IsFiveCycle sigma0 :=
  isFiveCycle_formPerm _ (by decide) (by decide)

theorem commutator_alpha0_beta0 : alpha0 * beta0 * alpha0⁻¹ * beta0⁻¹ = sigma0 := by
  unfold alpha0 beta0 sigma0
  decide

/-- Every five-cycle of `S₅` is a commutator of two five-cycles. -/
theorem exists_commutator_eq (σ : Perm5) (hσ : IsFiveCycle σ) :
    ∃ α β : Perm5, IsFiveCycle α ∧ IsFiveCycle β ∧ α * β * α⁻¹ * β⁻¹ = σ := by
  obtain ⟨ρ, hρ⟩ := isFiveCycle_sigma0.exists_conj hσ
  refine ⟨ρ * alpha0 * ρ⁻¹, ρ * beta0 * ρ⁻¹, isFiveCycle_alpha0.conj ρ,
    isFiveCycle_beta0.conj ρ, ?_⟩
  rw [← hρ, ← commutator_alpha0_beta0]
  group

/-! ### Multiplying the output of a program by a constant on the left -/

/-- Multiply the permutations produced by an instruction by `τ` on the left. -/
def Instr.lmul {n : ℕ} (τ : Perm5) : Instr n → Instr n
  | .test i p q => .test i (τ * p) (τ * q)
  | .const p => .const (τ * p)

/-- Multiply the output of a branching program by `τ` on the left, without increasing its
length (except for the empty program). -/
def lmulBP {n : ℕ} (τ : Perm5) : List (Instr n) → List (Instr n)
  | [] => [.const τ]
  | I :: t => I.lmul τ :: t

theorem BPeval_lmulBP {n : ℕ} (τ : Perm5) (P : List (Instr n)) (x : Fin n → Bool) :
    BPeval (lmulBP τ P) x = τ * BPeval P x := by
  cases P with
  | nil => simp [lmulBP, Instr.run, BPeval]
  | cons I t =>
      cases I with
      | test i p q =>
          by_cases h : x i <;> simp [lmulBP, Instr.lmul, Instr.run, h, mul_assoc]
      | const p => simp [lmulBP, Instr.lmul, Instr.run, mul_assoc]

theorem length_lmulBP {n : ℕ} (τ : Perm5) (P : List (Instr n)) :
    (lmulBP τ P).length = max P.length 1 := by
  cases P <;> simp [lmulBP]

/-! ### Removing constant instructions -/

/-- Replace a constant instruction by an instruction reading the input bit `i`. -/
def Instr.deconst {n : ℕ} (i : Fin n) : Instr n → Instr n
  | .const p => .test i p p
  | .test j p q => .test j p q

theorem Instr.run_deconst {n : ℕ} (i : Fin n) (I : Instr n) (x : Fin n → Bool) :
    (I.deconst i).run x = I.run x := by
  cases I <;> simp [Instr.deconst, Instr.run]

/-- Rewrite a program in the standard model, in which every instruction reads an input
bit.  This is possible as soon as there is at least one input bit. -/
def deconstBP {n : ℕ} (i : Fin n) (P : List (Instr n)) : List (Instr n) :=
  P.map (Instr.deconst i)

theorem BPeval_deconstBP {n : ℕ} (i : Fin n) (P : List (Instr n)) (x : Fin n → Bool) :
    BPeval (deconstBP i P) x = BPeval P x := by
  simp [BPeval, deconstBP, List.map_map, Function.comp_def, Instr.run_deconst]

theorem length_deconstBP {n : ℕ} (i : Fin n) (P : List (Instr n)) :
    (deconstBP i P).length = P.length := by
  simp [deconstBP]

theorem constFree_deconstBP {n : ℕ} (i : Fin n) (P : List (Instr n)) :
    ConstFree (deconstBP i P) := by
  intro I hI p
  simp only [deconstBP, List.mem_map] at hI
  obtain ⟨J, -, rfl⟩ := hI
  cases J <;> simp [Instr.deconst]

/-! ### The basic constructions -/

theorem bp_not {n : ℕ} {P : List (Instr n)} {σ : Perm5} {f : (Fin n → Bool) → Bool}
    (h : Computes P σ⁻¹ f) : Computes (lmulBP σ P) σ (fun x => !f x) := by
  intro x
  rw [BPeval_lmulBP, h x]
  cases hf : f x <;> simp [hf]

theorem bp_and {n : ℕ} {P₁ P₂ P₃ P₄ : List (Instr n)} {α β : Perm5}
    {f g : (Fin n → Bool) → Bool}
    (h1 : Computes P₁ α f) (h2 : Computes P₂ β g)
    (h3 : Computes P₃ α⁻¹ f) (h4 : Computes P₄ β⁻¹ g) :
    Computes (P₁ ++ P₂ ++ P₃ ++ P₄) (α * β * α⁻¹ * β⁻¹) (fun x => f x && g x) := by
  intro x
  rw [BPeval_append, BPeval_append, BPeval_append, h1 x, h2 x, h3 x, h4 x]
  cases hf : f x <;> cases hg : g x <;> simp [hf, hg, mul_assoc]

/-! ### Barrington's construction -/

/-- **Barrington's theorem** (hard direction): a formula of depth `d` is computed by a
width-5 permutation branching program of length at most `4 ^ d`, in normal form with
respect to any prescribed five-cycle. -/
theorem barrington_formula {n : ℕ} (φ : Formula n) :
    ∀ σ : Perm5, IsFiveCycle σ →
      ∃ P : List (Instr n), P.length ≤ 4 ^ φ.depth ∧ Computes P σ φ.eval := by
  induction φ with
  | const b =>
      intro σ _
      cases b with
      | true =>
          refine ⟨[.const σ], by simp [Formula.depth], ?_⟩
          intro x; simp [BPeval, Instr.run, Formula.eval]
      | false =>
          refine ⟨[], by simp, ?_⟩
          intro x; simp [Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[.test i σ 1], by simp [Formula.depth], ?_⟩
      intro x
      by_cases h : x i <;> simp [BPeval, Instr.run, Formula.eval, h]
  | not p ih =>
      intro σ hσ
      obtain ⟨P, hlen, hP⟩ := ih σ⁻¹ hσ.inv
      refine ⟨lmulBP σ P, ?_, ?_⟩
      · rw [length_lmulBP]
        have h1 : (1 : ℕ) ≤ 4 ^ p.depth := Nat.one_le_pow _ _ (by norm_num)
        have h2 : 4 ^ p.depth ≤ 4 ^ (p.depth + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [Formula.depth, max_le_iff]
        exact ⟨le_trans hlen h2, le_trans h1 h2⟩
      · exact bp_not hP
  | and p q ihp ihq =>
      intro σ hσ
      obtain ⟨α, β, hα, hβ, hcomm⟩ := exists_commutator_eq σ hσ
      obtain ⟨P₁, hl1, hP1⟩ := ihp α hα
      obtain ⟨P₂, hl2, hP2⟩ := ihq β hβ
      obtain ⟨P₃, hl3, hP3⟩ := ihp α⁻¹ hα.inv
      obtain ⟨P₄, hl4, hP4⟩ := ihq β⁻¹ hβ.inv
      refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, ?_, ?_⟩
      · have hm : ∀ d : ℕ, d ≤ max p.depth q.depth → (4:ℕ) ^ d ≤ 4 ^ (max p.depth q.depth) :=
          fun d hd => Nat.pow_le_pow_right (by norm_num) hd
        have e1 := hm p.depth (le_max_left _ _)
        have e2 := hm q.depth (le_max_right _ _)
        simp only [List.length_append, Formula.depth, pow_succ]
        omega
      · rw [← hcomm]
        exact bp_and hP1 hP2 hP3 hP4
  | or p q ihp ihq =>
      intro σ hσ
      obtain ⟨α, β, hα, hβ, hcomm⟩ := exists_commutator_eq σ⁻¹ hσ.inv
      -- programs for the negations of `p` and `q`
      have hnot : ∀ (r : Formula n),
          (∀ γ : Perm5, IsFiveCycle γ →
            ∃ P : List (Instr n), P.length ≤ 4 ^ r.depth ∧ Computes P γ r.eval) →
          ∀ γ : Perm5, IsFiveCycle γ →
            ∃ P : List (Instr n), P.length ≤ 4 ^ r.depth ∧
              Computes P γ (fun x => !r.eval x) := by
        intro r ihr γ hγ
        obtain ⟨P, hlen, hP⟩ := ihr γ⁻¹ hγ.inv
        refine ⟨lmulBP γ P, ?_, bp_not hP⟩
        rw [length_lmulBP]
        have h1 : (1 : ℕ) ≤ 4 ^ r.depth := Nat.one_le_pow _ _ (by norm_num)
        omega
      obtain ⟨P₁, hl1, hP1⟩ := hnot p ihp α hα
      obtain ⟨P₂, hl2, hP2⟩ := hnot q ihq β hβ
      obtain ⟨P₃, hl3, hP3⟩ := hnot p ihp α⁻¹ hα.inv
      obtain ⟨P₄, hl4, hP4⟩ := hnot q ihq β⁻¹ hβ.inv
      have hQ : Computes (P₁ ++ P₂ ++ P₃ ++ P₄) σ⁻¹
          (fun x => (!p.eval x) && (!q.eval x)) := by
        rw [← hcomm]; exact bp_and hP1 hP2 hP3 hP4
      refine ⟨lmulBP σ (P₁ ++ P₂ ++ P₃ ++ P₄), ?_, ?_⟩
      · rw [length_lmulBP]
        have hm : ∀ d : ℕ, d ≤ max p.depth q.depth → (4:ℕ) ^ d ≤ 4 ^ (max p.depth q.depth) :=
          fun d hd => Nat.pow_le_pow_right (by norm_num) hd
        have e1 := hm p.depth (le_max_left _ _)
        have e2 := hm q.depth (le_max_right _ _)
        have h1 : (1 : ℕ) ≤ 4 ^ (max p.depth q.depth) := Nat.one_le_pow _ _ (by norm_num)
        simp only [List.length_append, Formula.depth, pow_succ, max_le_iff]
        omega
      · have := bp_not hQ
        intro x
        have hx := this x
        simpa [Formula.eval, Bool.not_and, Bool.or_comm] using hx

end CS

import RequestProject.Basic
import RequestProject.Forward
import RequestProject.Backward

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

`NC¹` (non-uniform: families of boolean functions computed by fan-in two boolean formulas
of logarithmic depth, `CS.InNC1`) coincides with the class of families of boolean functions
computed by polynomial-length width-5 permutation branching programs (`CS.InW5BP`).

The hard direction is Barrington's construction (`CS.barrington_formula`): a formula of
depth `d` is simulated by a program of length at most `4 ^ d`, in normal form with respect
to any prescribed five-cycle.  The easy direction (`CS.exists_formula_of_bp`) is a divide
and conquer simulation of a program of length `ℓ` by a formula of depth `O(log ℓ)`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Equiv Equiv.Perm

theorem two_pow_log_le (n : ℕ) : (2 : ℕ) ^ (Nat.log 2 (n + 1) + 1) ≤ 2 * (n + 1) := by
  have hp : (2 : ℕ) ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  rw [pow_succ]
  omega

theorem le_two_pow_log (n : ℕ) : n + 1 ≤ 2 ^ (Nat.log 2 (n + 1) + 1) :=
  le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (n + 1))

/-- Every `NC¹` family is computed by polynomial-length width-5 permutation branching
programs. -/
theorem nc1_to_w5bp (f : (n : ℕ) → (Fin n → Bool) → Bool) (h : InNC1 f) : InW5BP f := by
  obtain ⟨c, fml, hfml⟩ := h
  choose P hlen hP using fun n =>
    barrington_formula (fml n) sigma0 isFiveCycle_sigma0
  refine ⟨2 ^ (2 * c) + 2 * c,
    fun n => if 0 < n then {sigma0} else (if f 0 (fun i => i.elim0) then {1} else ∅),
    fun n => if h : 0 < n then deconstBP ⟨0, h⟩ (P n) else [], fun n => ⟨?_, ?_, ?_⟩⟩
  · -- the length bound
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    simp only [dif_pos hn, length_deconstBP]
    set L := Nat.log 2 (n + 1) + 1 with hL
    have h1 : (P n).length ≤ 4 ^ (c * L) :=
      le_trans (hlen n) (Nat.pow_le_pow_right (by norm_num) (hfml n).2)
    have h2 : (4 : ℕ) ^ (c * L) = (2 ^ L) ^ (2 * c) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have h3 : (2 : ℕ) ^ L ≤ 2 * (n + 1) := by rw [hL]; exact two_pow_log_le n
    have h4 : ((2 : ℕ) ^ L) ^ (2 * c) ≤ (2 * (n + 1)) ^ (2 * c) := Nat.pow_le_pow_left h3 _
    have h5 : (2 * (n + 1)) ^ (2 * c) = 2 ^ (2 * c) * (n + 1) ^ (2 * c) := mul_pow _ _ _
    have h6 : (n + 1) ^ (2 * c) ≤ (n + 1) ^ (2 ^ (2 * c) + 2 * c) :=
      Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_add_left _ _)
    have h7 : (2 : ℕ) ^ (2 * c) * (n + 1) ^ (2 * c)
        ≤ (2 ^ (2 * c) + 2 * c) * (n + 1) ^ (2 ^ (2 * c) + 2 * c) :=
      Nat.mul_le_mul (by omega) h6
    omega
  · -- the program only reads input bits
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ConstFree]
    simpa only [dif_pos hn] using constFree_deconstBP (n := n) ⟨0, hn⟩ (P n)
  · -- the acceptance condition
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · intro x
      have hx : x = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      subst hx
      cases hf0 : f 0 (fun i : Fin 0 => i.elim0) <;> simp
    intro x
    simp only [dif_pos hn, if_pos hn, BPeval_deconstBP]
    have hx := hP n x
    rw [(hfml n).1 x] at hx
    rw [hx, Finset.mem_singleton]
    cases hfx : f n x with
    | true => simp
    | false => simpa using fun hc => isFiveCycle_sigma0.ne_one hc.symm

/-- Every family computed by polynomial-length width-5 permutation branching programs is in
`NC¹`. -/
theorem w5bp_to_nc1 (f : (n : ℕ) → (Fin n → Bool) → Bool) (h : InW5BP f) : InNC1 f := by
  obtain ⟨c, A, P, hP⟩ := h
  choose fml hfml hd using fun n => exists_formula_of_bp (P n) (A n)
  refine ⟨(K5 + 1) * (2 * c) + (K5 + 1), fml, fun n => ⟨fun x => ?_, ?_⟩⟩
  · exact Bool.eq_iff_iff.2 ((hfml n x).trans ((hP n).2.2 x).symm)
  · set L := Nat.log 2 (n + 1) + 1 with hL
    have hL1 : 1 ≤ L := by omega
    -- bound the logarithm of the length of the program
    have hlen : (P n).length ≤ 2 ^ (c + c * L) := by
      refine le_trans (hP n).1 ?_
      have h1 : c ≤ 2 ^ c := Nat.le_of_lt (Nat.lt_two_pow_self)
      have h2 : n + 1 ≤ 2 ^ L := by rw [hL]; exact le_two_pow_log n
      have h3 : (n + 1) ^ c ≤ (2 ^ L) ^ c := Nat.pow_le_pow_left h2 c
      have h4 : ((2 : ℕ) ^ L) ^ c = 2 ^ (c * L) := by rw [← pow_mul]; congr 1; ring
      calc c * (n + 1) ^ c ≤ 2 ^ c * 2 ^ (c * L) := by
            rw [← h4]; exact Nat.mul_le_mul h1 h3
        _ = 2 ^ (c + c * L) := by rw [← pow_add]
    have hclog : Nat.clog 2 (P n).length ≤ c + c * L :=
      (Nat.clog_le_iff_le_pow (by norm_num)).2 hlen
    -- turn the bound on the length into a bound on the depth
    have hstep : (K5 + 1) * Nat.clog 2 (P n).length + 1 + K5
        ≤ (K5 + 1) * (2 * c) * L + (K5 + 1) * L := by
      have hcc : c ≤ c * L := Nat.le_mul_of_pos_right c (by omega)
      have hcc2 : 2 * c * L = c * L + c * L := by ring
      have e1 : (K5 + 1) * Nat.clog 2 (P n).length ≤ (K5 + 1) * (2 * c * L) :=
        Nat.mul_le_mul_left _ (by omega)
      have e2 : (K5 + 1) * (2 * c * L) = (K5 + 1) * (2 * c) * L := by ring
      have e3 : (K5 + 1) ≤ (K5 + 1) * L := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hfin : (K5 + 1) * (2 * c) * L + (K5 + 1) * L
        = ((K5 + 1) * (2 * c) + (K5 + 1)) * L := by ring
    exact le_trans (le_trans (hd n) hstep) (le_of_eq hfin)

/-- **Barrington's theorem**: a family of boolean functions is in (non-uniform) `NC¹` if and
only if it is computed by polynomial-length width-5 permutation branching programs. -/
theorem barrington (f : (n : ℕ) → (Fin n → Bool) → Bool) : InNC1 f ↔ InW5BP f :=
  ⟨nc1_to_w5bp f, w5bp_to_nc1 f⟩

end CS

