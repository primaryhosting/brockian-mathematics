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

We formalise Barrington's theorem: the class of Boolean function families computed by
logarithmic-depth fan-in-two Boolean circuits (`NC¹`) coincides with the class of families
computed by polynomial-length width-`5` permutation branching programs.

* `CS.Barrington.Circuit` : fan-in two Boolean circuits over `{¬, ∧, ∨}` and constants.
* `CS.Barrington.Instr`, `CS.Barrington.run` : width-5 permutation branching programs,
  i.e. lists of instructions, each of which multiplies the running value in `S₅` by a
  permutation depending on (at most) one input bit.
* `CS.Barrington.NC1` and `CS.Barrington.W5BP` : the two classes.
* `CS.barrington` : the two classes are equal.
-/

namespace CS
namespace Barrington

open Equiv

/-- The symmetric group on five points. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-! ### Boolean circuits -/

/-- Fan-in two Boolean circuits (formulas) on `n` inputs. -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- The Boolean function computed by a circuit. -/
def Circuit.eval {n : ℕ} : Circuit n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .const b, _ => b
  | .not c, x => !(c.eval x)
  | .and c d, x => (c.eval x) && (d.eval x)
  | .or c d, x => (c.eval x) || (d.eval x)

/-- The depth of a circuit. -/
def Circuit.depth {n : ℕ} : Circuit n → ℕ
  | .var _ => 0
  | .const _ => 0
  | .not c => c.depth + 1
  | .and c d => max c.depth d.depth + 1
  | .or c d => max c.depth d.depth + 1

/-! ### Width-5 permutation branching programs -/

/-- An instruction of a width-5 permutation branching program: either a fixed permutation,
or a permutation depending on the value of one input bit. -/
inductive Instr (n : ℕ) where
  | const : Perm5 → Instr n
  | query : Fin n → Perm5 → Perm5 → Instr n

/-- The permutation contributed by an instruction on a given input. -/
def Instr.run {n : ℕ} : Instr n → (Fin n → Bool) → Perm5
  | .const g, _ => g
  | .query i g₀ g₁, x => if x i then g₁ else g₀

/-- The permutation computed by a program: the ordered product of its instructions. -/
def run {n : ℕ} (P : List (Instr n)) (x : Fin n → Bool) : Perm5 :=
  (P.map (fun i => i.run x)).prod

/-- `P` computes the function `f` with distinguished permutation `σ`. -/
def Comp {n : ℕ} (P : List (Instr n)) (f : (Fin n → Bool) → Bool) (σ : Perm5) : Prop :=
  ∀ x, run P x = if f x then σ else 1

/-- A branching program computes a Boolean function if it outputs a fixed non-identity
permutation exactly on the accepted inputs, and the identity otherwise. -/
def BPComputes {n : ℕ} (P : List (Instr n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ σ : Perm5, σ ≠ 1 ∧ Comp P f σ

/-! ### The two classes -/

/-- `NC¹`: families of Boolean functions computed by fan-in two circuits of depth
`O(log n)`. -/
def NC1 (f : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ (C : (n : ℕ) → Circuit n) (c : ℕ), ∀ n,
    (∀ x, (C n).eval x = f n x) ∧ (C n).depth ≤ c * Nat.log 2 (n + 1) + c

/-- Families of Boolean functions computed by width-5 permutation branching programs of
polynomial length. -/
def W5BP (f : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ (P : (n : ℕ) → List (Instr n)) (c : ℕ), ∀ n,
    BPComputes (P n) (f n) ∧ (P n).length ≤ c * (n + 1) ^ c + c

/-! ### Basic facts about programs -/

@[simp] lemma run_nil {n : ℕ} (x : Fin n → Bool) : run ([] : List (Instr n)) x = 1 := by
  simp [run]

@[simp] lemma run_cons {n : ℕ} (i : Instr n) (P : List (Instr n)) (x : Fin n → Bool) :
    run (i :: P) x = i.run x * run P x := by
  simp [run]

@[simp] lemma run_append {n : ℕ} (P Q : List (Instr n)) (x : Fin n → Bool) :
    run (P ++ Q) x = run P x * run Q x := by
  simp [run]

/-- Multiply an instruction on the right by a fixed permutation. -/
def Instr.mulRight {n : ℕ} : Instr n → Perm5 → Instr n
  | .const h, g => .const (h * g)
  | .query i h₀ h₁, g => .query i (h₀ * g) (h₁ * g)

@[simp] lemma Instr.run_mulRight {n : ℕ} (i : Instr n) (g : Perm5) (x : Fin n → Bool) :
    (i.mulRight g).run x = i.run x * g := by
  cases i with
  | const h => rfl
  | query j h₀ h₁ => by_cases h : x j <;> simp [Instr.mulRight, Instr.run, h]

/-- Any program can be modified, without increasing its length (beyond `1`), so that its
output is multiplied on the right by a fixed permutation. -/
lemma exists_mulRight {n : ℕ} (P : List (Instr n)) (g : Perm5) :
    ∃ Q : List (Instr n), (∀ x, run Q x = run P x * g) ∧ Q.length ≤ max 1 P.length := by
  rcases List.eq_nil_or_concat P with h | ⟨L, i, h⟩
  · subst h
    exact ⟨[Instr.const g], fun x => by simp [Instr.run], by simp⟩
  · subst h
    refine ⟨L.concat (i.mulRight g), fun x => ?_, ?_⟩
    · simp [List.concat_eq_append, mul_assoc]
    · simp [List.concat_eq_append]

/-! ### The five-cycle bookkeeping -/

/-- A distinguished 5-cycle. -/
def c5 : Perm5 := List.formPerm [0, 1, 2, 3, 4]

lemma c5_ne_one : c5 ≠ 1 := by decide

lemma conj_ne_one (ρ : Perm5) : ρ * c5 * ρ⁻¹ ≠ 1 := by
  intro h
  refine c5_ne_one ?_
  have h' := congrArg (fun t => ρ⁻¹ * t * ρ) h
  simpa [mul_assoc] using h'

/-- The inverse of a conjugate of `c5` is again a conjugate of `c5`. -/
lemma exists_conj_inv (ρ : Perm5) : ∃ ρ' : Perm5, ρ' * c5 * ρ'⁻¹ = (ρ * c5 * ρ⁻¹)⁻¹ := by
  obtain ⟨θ, hθ⟩ : ∃ θ : Perm5, θ * c5 * θ⁻¹ = c5⁻¹ := by decide
  refine ⟨ρ * θ, ?_⟩
  have h1 : (ρ * c5 * ρ⁻¹)⁻¹ = ρ * c5⁻¹ * ρ⁻¹ := by group
  rw [h1, ← hθ]
  group

/-- Every conjugate of `c5` is a commutator of two conjugates of `c5`. -/
lemma exists_conj_commutator (ρ : Perm5) :
    ∃ a b : Perm5,
      (a * c5 * a⁻¹) * (b * c5 * b⁻¹) * (a * c5 * a⁻¹)⁻¹ * (b * c5 * b⁻¹)⁻¹ = ρ * c5 * ρ⁻¹ := by
  obtain ⟨u, hu⟩ : ∃ u : Perm5, u * c5 * u⁻¹ = List.formPerm [2, 1, 3, 0, 4] := by decide
  obtain ⟨v, hv⟩ : ∃ v : Perm5, v * c5 * v⁻¹ = List.formPerm [2, 0, 1, 3, 4] := by decide
  have key : (List.formPerm [2, 1, 3, 0, 4] : Perm5) * (List.formPerm [2, 0, 1, 3, 4]) *
      (List.formPerm [2, 1, 3, 0, 4] : Perm5)⁻¹ * (List.formPerm [2, 0, 1, 3, 4] : Perm5)⁻¹
      = c5 := by decide
  refine ⟨ρ * u, ρ * v, ?_⟩
  have e1 : (ρ * u) * c5 * (ρ * u)⁻¹ = ρ * (List.formPerm [2, 1, 3, 0, 4] : Perm5) * ρ⁻¹ := by
    rw [← hu]; group
  have e2 : (ρ * v) * c5 * (ρ * v)⁻¹ = ρ * (List.formPerm [2, 0, 1, 3, 4] : Perm5) * ρ⁻¹ := by
    rw [← hv]; group
  rw [e1, e2, ← key]
  group

/-! ### From circuits to branching programs (Barrington's construction) -/

/-- There is a program of length at most `N` computing `f` with distinguished
permutation `σ`. -/
def CompLen {n : ℕ} (f : (Fin n → Bool) → Bool) (σ : Perm5) (N : ℕ) : Prop :=
  ∃ P : List (Instr n), Comp P f σ ∧ P.length ≤ N

lemma CompLen.of_eq {n : ℕ} {f g : (Fin n → Bool) → Bool} {σ : Perm5} {N : ℕ}
    (h : CompLen f σ N) (hfg : ∀ x, f x = g x) : CompLen g σ N := by
  obtain ⟨P, hP, hlen⟩ := h
  exact ⟨P, fun x => by rw [hP x, hfg x], hlen⟩

lemma CompLen.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {σ : Perm5} {N M : ℕ}
    (h : CompLen f σ N) (hNM : N ≤ M) : CompLen f σ M := by
  obtain ⟨P, hP, hlen⟩ := h
  exact ⟨P, hP, hlen.trans hNM⟩

/-- Negation is free (up to length one). -/
lemma CompLen.neg {n : ℕ} {f : (Fin n → Bool) → Bool} {σ : Perm5} {N : ℕ}
    (h : CompLen f σ⁻¹ N) : CompLen (fun x => !f x) σ (max 1 N) := by
  obtain ⟨P, hP, hlen⟩ := h
  obtain ⟨Q, hQ, hQlen⟩ := exists_mulRight P σ
  refine ⟨Q, fun x => ?_, hQlen.trans (max_le_max le_rfl hlen)⟩
  rw [hQ x, hP x]
  by_cases hx : f x <;> simp [hx]

/-- The commutator trick. -/
lemma CompLen.commutator {n : ℕ} {f g : (Fin n → Bool) → Bool} {A B : Perm5} {N M : ℕ}
    (h₁ : CompLen f A N) (h₂ : CompLen g B M)
    (h₃ : CompLen f A⁻¹ N) (h₄ : CompLen g B⁻¹ M) :
    CompLen (fun x => f x && g x) (A * B * A⁻¹ * B⁻¹) (N + M + N + M) := by
  obtain ⟨P₁, hP₁, l₁⟩ := h₁
  obtain ⟨P₂, hP₂, l₂⟩ := h₂
  obtain ⟨P₃, hP₃, l₃⟩ := h₃
  obtain ⟨P₄, hP₄, l₄⟩ := h₄
  refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, fun x => ?_, ?_⟩
  · simp only [run_append, hP₁ x, hP₂ x, hP₃ x, hP₄ x]
    by_cases hf : f x <;> by_cases hg : g x <;> simp [hf, hg]
  · simp only [List.length_append]
    omega

/-- **Barrington's construction**: a circuit of depth `d` is simulated by a width-5
permutation branching program of length at most `4 ^ d`, computing the given conjugate
of the 5-cycle `c5`. -/
theorem circuit_to_bp {n : ℕ} (C : Circuit n) :
    ∀ ρ : Perm5, CompLen C.eval (ρ * c5 * ρ⁻¹) (4 ^ C.depth) := by
  induction C with
  | var i =>
      intro ρ
      refine ⟨[Instr.query i 1 (ρ * c5 * ρ⁻¹)], fun x => ?_, by simp [Circuit.depth]⟩
      by_cases hx : x i <;> simp [Circuit.eval, Instr.run, hx]
  | const b =>
      intro ρ
      cases b
      · exact ⟨[], fun x => by simp [Circuit.eval], by simp⟩
      · exact ⟨[Instr.const (ρ * c5 * ρ⁻¹)], fun x => by simp [Circuit.eval, Instr.run], by simp [Circuit.depth]⟩
  | not C ih =>
      intro ρ
      obtain ⟨ρ', hρ'⟩ := exists_conj_inv ρ
      have h := ih ρ'
      rw [hρ'] at h
      have h2 := h.neg
      have h3 : CompLen (Circuit.not C).eval (ρ * c5 * ρ⁻¹) (max 1 (4 ^ C.depth)) :=
        h2.of_eq (fun x => rfl)
      refine h3.mono ?_
      have h4 : (1 : ℕ) ≤ 4 ^ C.depth := Nat.one_le_pow _ _ (by norm_num)
      have h5 : 4 ^ C.depth ≤ 4 ^ (C.depth + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [Circuit.depth]
      omega
  | and C D ihC ihD =>
      intro ρ
      obtain ⟨a, b, hab⟩ := exists_conj_commutator ρ
      obtain ⟨a', ha'⟩ := exists_conj_inv a
      obtain ⟨b', hb'⟩ := exists_conj_inv b
      have h1 := ihC a
      have h2 := ihD b
      have h3 := ihC a'
      have h4 := ihD b'
      rw [ha'] at h3
      rw [hb'] at h4
      have hcomm := CompLen.commutator h1 h2 h3 h4
      rw [hab] at hcomm
      have h5 : CompLen (Circuit.and C D).eval (ρ * c5 * ρ⁻¹)
          (4 ^ C.depth + 4 ^ D.depth + 4 ^ C.depth + 4 ^ D.depth) := hcomm.of_eq (fun x => rfl)
      refine h5.mono ?_
      have hC : (4 : ℕ) ^ C.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hD : (4 : ℕ) ^ D.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : (4 : ℕ) ^ (max C.depth D.depth + 1) = 4 * 4 ^ (max C.depth D.depth) := by ring
      simp only [Circuit.depth, this]
      omega
  | or C D ihC ihD =>
      intro ρ
      obtain ⟨ρ', hρ'⟩ := exists_conj_inv ρ
      obtain ⟨a, b, hab⟩ := exists_conj_commutator ρ'
      obtain ⟨a', ha'⟩ := exists_conj_inv a
      obtain ⟨b', hb'⟩ := exists_conj_inv b
      -- programs for the negations
      have n1 : CompLen (fun x => !C.eval x) (a * c5 * a⁻¹) (max 1 (4 ^ C.depth)) := by
        have := ihC a'
        rw [ha'] at this
        exact this.neg
      have n2 : CompLen (fun x => !D.eval x) (b * c5 * b⁻¹) (max 1 (4 ^ D.depth)) := by
        have := ihD b'
        rw [hb'] at this
        exact this.neg
      have n3 : CompLen (fun x => !C.eval x) (a * c5 * a⁻¹)⁻¹ (max 1 (4 ^ C.depth)) := by
        have := ihC a
        rw [← inv_inv (a * c5 * a⁻¹)] at this
        exact this.neg
      have n4 : CompLen (fun x => !D.eval x) (b * c5 * b⁻¹)⁻¹ (max 1 (4 ^ D.depth)) := by
        have := ihD b
        rw [← inv_inv (b * c5 * b⁻¹)] at this
        exact this.neg
      have hcomm := CompLen.commutator n1 n2 n3 n4
      rw [hab, hρ'] at hcomm
      have hneg := hcomm.neg
      have h5 : CompLen (Circuit.or C D).eval (ρ * c5 * ρ⁻¹)
          (max 1 (max 1 (4 ^ C.depth) + max 1 (4 ^ D.depth) + max 1 (4 ^ C.depth) +
            max 1 (4 ^ D.depth))) := by
        refine hneg.of_eq (fun x => ?_)
        simp [Circuit.eval]
      refine h5.mono ?_
      have hC1 : (1 : ℕ) ≤ 4 ^ C.depth := Nat.one_le_pow _ _ (by norm_num)
      have hD1 : (1 : ℕ) ≤ 4 ^ D.depth := Nat.one_le_pow _ _ (by norm_num)
      have hC : (4 : ℕ) ^ C.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hD : (4 : ℕ) ^ D.depth ≤ 4 ^ (max C.depth D.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have h6 : (4 : ℕ) ^ (max C.depth D.depth + 1) = 4 * 4 ^ (max C.depth D.depth) := by ring
      have h7 : (1 : ℕ) ≤ 4 ^ (max C.depth D.depth) := Nat.one_le_pow _ _ (by norm_num)
      simp only [Circuit.depth, h6]
      omega

/-! ### From branching programs to circuits -/

/-- A balanced disjunction of a list of circuits, with fuel `k`. -/
def bigOr {n : ℕ} : ℕ → List (Circuit n) → Circuit n
  | 0, l => l.headD (Circuit.const false)
  | (k + 1), l =>
      if l.length ≤ 1 then l.headD (Circuit.const false)
      else Circuit.or (bigOr k (l.take (l.length / 2))) (bigOr k (l.drop (l.length / 2)))

lemma bigOr_eval {n : ℕ} (k : ℕ) (l : List (Circuit n)) (hl : l.length ≤ 2 ^ k)
    (x : Fin n → Bool) : (bigOr k l).eval x = l.any (fun c => c.eval x) := by
  induction k generalizing l with
  | zero =>
      rcases l with _ | ⟨c, l⟩
      · simp [bigOr, Circuit.eval]
      · rcases l with _ | ⟨d, l⟩
        · simp [bigOr]
        · simp at hl
  | succ k ih =>
      by_cases h : l.length ≤ 1
      · simp only [bigOr, if_pos h]
        rcases l with _ | ⟨c, l⟩
        · simp [Circuit.eval]
        · rcases l with _ | ⟨d, l⟩
          · simp
          · simp at h
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have ht : (l.take (l.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_take]
          omega
        have hd : (l.drop (l.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_drop]
          omega
        simp only [bigOr, if_neg h, Circuit.eval, ih _ ht, ih _ hd]
        conv_rhs => rw [← List.take_append_drop (l.length / 2) l]
        rw [List.any_append]

lemma bigOr_depth {n : ℕ} (k : ℕ) (l : List (Circuit n)) (D : ℕ)
    (hD : ∀ c ∈ l, c.depth ≤ D) : (bigOr k l).depth ≤ D + k := by
  induction k generalizing l with
  | zero =>
      rcases l with _ | ⟨c, l⟩
      · simp [bigOr, Circuit.depth]
      · simpa [bigOr] using hD c (by simp)
  | succ k ih =>
      by_cases h : l.length ≤ 1
      · simp only [bigOr, if_pos h]
        rcases l with _ | ⟨c, l⟩
        · simp [Circuit.depth]
        · have := hD c (by simp)
          simpa using by omega
      · have ht : ∀ c ∈ l.take (l.length / 2), c.depth ≤ D := fun c hc =>
          hD c ((List.take_sublist _ _).mem hc)
        have hdr : ∀ c ∈ l.drop (l.length / 2), c.depth ≤ D := fun c hc =>
          hD c ((List.drop_sublist _ _).mem hc)
        have h1 := ih (l.take (l.length / 2)) ht
        have h2 := ih (l.drop (l.length / 2)) hdr
        simp only [bigOr, if_neg h, Circuit.depth]
        omega

/-- The base case: a circuit deciding whether a program of length at most one outputs `g`. -/
def baseCirc {n : ℕ} : List (Instr n) → Perm5 → Circuit n
  | [], g => Circuit.const (decide ((1 : Perm5) = g))
  | (.const h) :: _, g => Circuit.const (decide (h = g))
  | (.query i h₀ h₁) :: _, g =>
      Circuit.or (Circuit.and (Circuit.not (Circuit.var i)) (Circuit.const (decide (h₀ = g))))
        (Circuit.and (Circuit.var i) (Circuit.const (decide (h₁ = g))))

lemma baseCirc_eval {n : ℕ} (P : List (Instr n)) (hP : P.length ≤ 1) (g : Perm5)
    (x : Fin n → Bool) : (baseCirc P g).eval x = decide (run P x = g) := by
  rcases P with _ | ⟨i, t⟩
  · simp [baseCirc, Circuit.eval]
  · have ht : t = [] := by
      rcases t with _ | ⟨j, t⟩
      · rfl
      · simp at hP
    subst ht
    cases i with
    | const h => simp [baseCirc, Circuit.eval, Instr.run]
    | query j h₀ h₁ =>
        by_cases hx : x j <;>
          simp [baseCirc, Circuit.eval, Instr.run, hx]

lemma baseCirc_depth {n : ℕ} (P : List (Instr n)) (g : Perm5) :
    (baseCirc P g).depth ≤ 3 := by
  rcases P with _ | ⟨i, t⟩
  · simp [baseCirc, Circuit.depth]
  · cases i with
    | const h => simp [baseCirc, Circuit.depth]
    | query j h₀ h₁ => simp [baseCirc, Circuit.depth]

/-- The list of all permutations of `Fin 5`. -/
noncomputable def allPerms : List Perm5 := (Finset.univ : Finset Perm5).toList

lemma allPerms_length : allPerms.length = 120 := by
  rw [allPerms, Finset.length_toList, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  decide

lemma mem_allPerms (h : Perm5) : h ∈ allPerms := by
  rw [allPerms, Finset.mem_toList]
  exact Finset.mem_univ h

/-- Splitting a product over all possible values of the first factor. -/
lemma any_prod_eq {n : ℕ} (T D : List (Instr n)) (x : Fin n → Bool) (g : Perm5) :
    (allPerms.any fun h => decide (run T x = h) && decide (run D x = h⁻¹ * g))
      = decide (run T x * run D x = g) := by
  refine Bool.eq_iff_iff.mpr ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [List.any_eq_true] at hb
    obtain ⟨h, -, hh⟩ := hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    simp [hh.1, hh.2]
  · simp only [decide_eq_true_eq] at hb
    rw [List.any_eq_true]
    refine ⟨run T x, mem_allPerms _, ?_⟩
    have hD : run D x = (run T x)⁻¹ * g := by rw [← hb]; group
    simp [hD]

/-- A circuit deciding whether the program `P` (of length at most `2 ^ k`) outputs `g`. -/
noncomputable def prodCirc {n : ℕ} : ℕ → List (Instr n) → Perm5 → Circuit n
  | 0, P, g => baseCirc P g
  | (k + 1), P, g =>
      if P.length ≤ 1 then baseCirc P g
      else bigOr 7 (allPerms.map (fun h =>
        Circuit.and (prodCirc k (P.take (P.length / 2)) h)
          (prodCirc k (P.drop (P.length / 2)) (h⁻¹ * g))))

lemma prodCirc_eval {n : ℕ} (k : ℕ) (P : List (Instr n)) (hP : P.length ≤ 2 ^ k) (g : Perm5)
    (x : Fin n → Bool) : (prodCirc k P g).eval x = decide (run P x = g) := by
  induction k generalizing P g with
  | zero =>
      simpa [prodCirc] using baseCirc_eval P (by simpa using hP) g x
  | succ k ih =>
      by_cases h : P.length ≤ 1
      · simp only [prodCirc, if_pos h]
        exact baseCirc_eval P h g x
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have ht : (P.take (P.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_take]; omega
        have hd : (P.drop (P.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_drop]; omega
        have hlen : (allPerms.map (fun h : Perm5 =>
            Circuit.and (prodCirc k (P.take (P.length / 2)) h)
              (prodCirc k (P.drop (P.length / 2)) (h⁻¹ * g)))).length ≤ 2 ^ 7 := by
          rw [List.length_map, allPerms_length]
          norm_num
        have hsplit : run P x = run (P.take (P.length / 2)) x * run (P.drop (P.length / 2)) x := by
          conv_lhs => rw [← List.take_append_drop (P.length / 2) P]
          rw [run_append]
        simp only [prodCirc, if_neg h]
        rw [bigOr_eval 7 _ hlen x, List.any_map]
        simp only [Function.comp_def, Circuit.eval, ih _ ht, ih _ hd]
        rw [hsplit]
        exact any_prod_eq _ _ x g

lemma prodCirc_depth {n : ℕ} (k : ℕ) (P : List (Instr n)) (g : Perm5) :
    (prodCirc k P g).depth ≤ 11 * k + 3 := by
  induction k generalizing P g with
  | zero => simpa [prodCirc] using baseCirc_depth P g
  | succ k ih =>
      by_cases h : P.length ≤ 1
      · simp only [prodCirc, if_pos h]
        have := baseCirc_depth P g
        omega
      · simp only [prodCirc, if_neg h]
        have hb := bigOr_depth (n := n) 7
          (allPerms.map (fun h : Perm5 =>
            Circuit.and (prodCirc k (P.take (P.length / 2)) h)
              (prodCirc k (P.drop (P.length / 2)) (h⁻¹ * g)))) (11 * k + 4) ?_
        · omega
        · intro c hc
          rw [List.mem_map] at hc
          obtain ⟨h', _, rfl⟩ := hc
          have h1 := ih (P.take (P.length / 2)) h'
          have h2 := ih (P.drop (P.length / 2)) (h'⁻¹ * g)
          simp only [Circuit.depth]
          omega

/-! ### The two directions -/

theorem nc1_to_w5bp {f : (n : ℕ) → (Fin n → Bool) → Bool} (hf : NC1 f) : W5BP f := by
  obtain ⟨C, c, hC⟩ := hf
  have key : ∀ n, ∃ Q : List (Instr n), Comp Q (f n) c5 ∧ Q.length ≤ 4 ^ (C n).depth := by
    intro n
    obtain ⟨Q, hQ, hlen⟩ := circuit_to_bp (C n) 1
    refine ⟨Q, fun x => ?_, hlen⟩
    rw [hQ x]
    simp [(hC n).1 x]
  choose Q hQ hlen using key
  refine ⟨Q, max (4 ^ c) (2 * c), fun n => ⟨⟨c5, c5_ne_one, hQ n⟩, ?_⟩⟩
  have h2L : (2 : ℕ) ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  have h4L : (4 : ℕ) ^ Nat.log 2 (n + 1) ≤ (n + 1) ^ 2 := by
    have : (4 : ℕ) ^ Nat.log 2 (n + 1) = (2 ^ Nat.log 2 (n + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [this]
    exact Nat.pow_le_pow_left h2L 2
  have hstep : (4 : ℕ) ^ (c * Nat.log 2 (n + 1) + c) ≤ 4 ^ c * (n + 1) ^ (2 * c) := by
    have h1 : (4 : ℕ) ^ (c * Nat.log 2 (n + 1) + c)
        = 4 ^ c * (4 ^ Nat.log 2 (n + 1)) ^ c := by
      rw [pow_add, pow_mul]
      ring
    have h2 : ((4 : ℕ) ^ Nat.log 2 (n + 1)) ^ c ≤ ((n + 1) ^ 2) ^ c := Nat.pow_le_pow_left h4L c
    have h3 : ((n + 1) ^ 2 : ℕ) ^ c = (n + 1) ^ (2 * c) := by rw [← pow_mul]
    rw [h1, ← h3]
    exact Nat.mul_le_mul_left _ h2
  have hd : (4 : ℕ) ^ (C n).depth ≤ 4 ^ (c * Nat.log 2 (n + 1) + c) :=
    Nat.pow_le_pow_right (by norm_num) (hC n).2
  have hK1 : (4 : ℕ) ^ c ≤ max (4 ^ c) (2 * c) := le_max_left _ _
  have hK2 : ((n : ℕ) + 1) ^ (2 * c) ≤ (n + 1) ^ max (4 ^ c) (2 * c) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc (Q n).length ≤ 4 ^ (C n).depth := hlen n
    _ ≤ 4 ^ (c * Nat.log 2 (n + 1) + c) := hd
    _ ≤ 4 ^ c * (n + 1) ^ (2 * c) := hstep
    _ ≤ max (4 ^ c) (2 * c) * (n + 1) ^ max (4 ^ c) (2 * c) := Nat.mul_le_mul hK1 hK2
    _ ≤ max (4 ^ c) (2 * c) * (n + 1) ^ max (4 ^ c) (2 * c) + max (4 ^ c) (2 * c) :=
        Nat.le_add_right _ _

theorem w5bp_to_nc1 {f : (n : ℕ) → (Fin n → Bool) → Bool} (hf : W5BP f) : NC1 f := by
  obtain ⟨P, c, hP⟩ := hf
  have key : ∀ n, ∃ D : Circuit n, (∀ x, D.eval x = f n x) ∧
      D.depth ≤ 11 * ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) + 3 := by
    intro n
    obtain ⟨⟨σ, hσ, hcomp⟩, hlen⟩ := hP n
    have hPlen : (P n).length ≤ 2 ^ ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) := by
      refine hlen.trans ?_
      have h1 : n + 1 ≤ 2 ^ (Nat.log 2 (n + 1) + 1) :=
        le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (n + 1))
      have h2 : ((n : ℕ) + 1) ^ (c + 1) ≤ (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (c + 1) :=
        Nat.pow_le_pow_left h1 _
      have hpow : (2 : ℕ) ^ ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1))
          = (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (c + 1) * 2 ^ (c + 1) := by
        rw [pow_add, ← pow_mul, mul_comm (c + 1) (Nat.log 2 (n + 1) + 1)]
      have h3 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
      have h4 : ((n : ℕ) + 1) ^ c ≤ (n + 1) ^ (c + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hY : (1 : ℕ) ≤ ((n : ℕ) + 1) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      have h6 : (2 * c + 2) * ((n : ℕ) + 1) ^ (c + 1)
          ≤ (2 ^ (Nat.log 2 (n + 1) + 1)) ^ (c + 1) * 2 ^ (c + 1) := by
        rw [mul_comm]
        refine Nat.mul_le_mul h2 ?_
        calc 2 * c + 2 ≤ 2 * 2 ^ c := by omega
          _ = 2 ^ (c + 1) := by ring
      have h7 : c * ((n : ℕ) + 1) ^ c + c ≤ (2 * c + 2) * ((n : ℕ) + 1) ^ (c + 1) := by
        have hcY : c * ((n : ℕ) + 1) ^ c ≤ c * ((n : ℕ) + 1) ^ (c + 1) :=
          Nat.mul_le_mul_left _ h4
        nlinarith [hY, hcY]
      rw [hpow]
      exact le_trans h7 h6
    refine ⟨prodCirc ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) (P n) σ, fun x => ?_,
      prodCirc_depth _ (P n) σ⟩
    rw [prodCirc_eval _ (P n) hPlen σ x, hcomp x]
    by_cases hx : f n x
    · simp [hx]
    · have hne : (1 : Perm5) ≠ σ := fun hh => hσ hh.symm
      simp [hx, hne]
  choose D hD1 hD2 using key
  refine ⟨D, 22 * (c + 1) + 3, fun n => ⟨hD1 n, ?_⟩⟩
  refine (hD2 n).trans ?_
  have hexp : 11 * ((c + 1) * (Nat.log 2 (n + 1) + 1) + (c + 1)) + 3
      = 11 * (c + 1) * Nat.log 2 (n + 1) + (22 * (c + 1) + 3) := by ring
  rw [hexp]
  have : 11 * (c + 1) * Nat.log 2 (n + 1) ≤ (22 * (c + 1) + 3) * Nat.log 2 (n + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Sanity check that the classes are not vacuous: the family "the first input bit" is
in `NC1`, hence (by `CS.barrington`) also in `W5BP`. -/
example : NC1 (fun n (x : Fin n → Bool) => if h : 0 < n then x ⟨0, h⟩ else false) := by
  refine ⟨fun n => if h : 0 < n then Circuit.var ⟨0, h⟩ else Circuit.const false, 0,
    fun n => ⟨fun x => ?_, ?_⟩⟩
  · by_cases h : 0 < n <;> simp [h, Circuit.eval]
  · by_cases h : 0 < n <;> simp [h, Circuit.depth]

theorem nc1_iff_w5bp (f : (n : ℕ) → (Fin n → Bool) → Bool) : NC1 f ↔ W5BP f :=
  ⟨nc1_to_w5bp, w5bp_to_nc1⟩

end Barrington

/-- **Barrington's theorem**: `NC¹` (families of Boolean functions computed by fan-in two
Boolean circuits of logarithmic depth) coincides with the class of families computed by
width-5 permutation branching programs of polynomial length. -/
theorem barrington :
    {f : (n : ℕ) → (Fin n → Bool) → Bool | Barrington.NC1 f} =
      {f : (n : ℕ) → (Fin n → Bool) → Bool | Barrington.W5BP f} :=
  Set.ext fun f => Barrington.nc1_iff_w5bp f

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

