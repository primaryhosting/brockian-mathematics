import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Arithmetical truth is not arithmetically definable (Tarski's undefinability theorem).

Everything is built from scratch: the syntax of first-order arithmetic (with named
variables), its satisfaction relation in the standard model `ℕ`, the notion of an
arithmetically definable set/relation, Gödel numberings, and the truth set.
-/

namespace Frontier

set_option autoImplicit false

/-! ## Syntax of first-order arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, *}`, with variables indexed by `ℕ`. -/
inductive ATerm : Type
  | var : ℕ → ATerm
  | zero : ATerm
  | succ : ATerm → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq, Encodable

/-- Formulas of the language of arithmetic.  `all i φ` is `∀ xᵢ, φ`. -/
inductive AForm : Type
  | eq : ATerm → ATerm → AForm
  | not : AForm → AForm
  | and : AForm → AForm → AForm
  | all : ℕ → AForm → AForm
  deriving DecidableEq, Encodable

instance : Inhabited AForm := ⟨AForm.eq ATerm.zero ATerm.zero⟩

/-- Evaluation of a term in the standard model `ℕ` under an assignment `ρ`. -/
def evalTerm : ATerm → (ℕ → ℕ) → ℕ
  | .var i, ρ => ρ i
  | .zero, _ => 0
  | .succ t, ρ => evalTerm t ρ + 1
  | .add s t, ρ => evalTerm s ρ + evalTerm t ρ
  | .mul s t, ρ => evalTerm s ρ * evalTerm t ρ

/-- Tarskian satisfaction in the standard model `ℕ`: `Sat φ ρ` means that the formula `φ`
is satisfied in `ℕ` by the assignment `ρ`. -/
def Sat : AForm → (ℕ → ℕ) → Prop
  | .eq s t, ρ => evalTerm s ρ = evalTerm t ρ
  | .not φ, ρ => ¬ Sat φ ρ
  | .and φ ψ, ρ => Sat φ ρ ∧ Sat ψ ρ
  | .all i φ, ρ => ∀ v, Sat φ (Function.update ρ i v)

@[simp] theorem Sat_eq (s t : ATerm) (ρ : ℕ → ℕ) :
    Sat (.eq s t) ρ ↔ evalTerm s ρ = evalTerm t ρ := Iff.rfl

@[simp] theorem Sat_not (φ : AForm) (ρ : ℕ → ℕ) : Sat (.not φ) ρ ↔ ¬ Sat φ ρ := Iff.rfl

@[simp] theorem Sat_and (φ ψ : AForm) (ρ : ℕ → ℕ) :
    Sat (.and φ ψ) ρ ↔ Sat φ ρ ∧ Sat ψ ρ := Iff.rfl

@[simp] theorem Sat_all (i : ℕ) (φ : AForm) (ρ : ℕ → ℕ) :
    Sat (.all i φ) ρ ↔ ∀ v, Sat φ (Function.update ρ i v) := Iff.rfl

/-- The numeral denoting `n`. -/
def numeral : ℕ → ATerm
  | 0 => .zero
  | n + 1 => .succ (numeral n)

@[simp] theorem evalTerm_numeral (n : ℕ) (ρ : ℕ → ℕ) : evalTerm (numeral n) ρ = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, evalTerm, ih]

theorem numeral_injective : Function.Injective numeral := by
  intro m n h
  induction m generalizing n with
  | zero => cases n with
    | zero => rfl
    | succ n => simp [numeral] at h
  | succ m ih =>
    cases n with
    | zero => simp [numeral] at h
    | succ n =>
      simp only [numeral, ATerm.succ.injEq] at h
      exact congrArg Nat.succ (ih h)

/-! ## Substitution of numerals -/

/-- Substitute the numeral for `k` in place of the variable `xᵢ` in a term. -/
def substTermNum (i k : ℕ) : ATerm → ATerm
  | .var j => if j = i then numeral k else .var j
  | .zero => .zero
  | .succ t => .succ (substTermNum i k t)
  | .add s t => .add (substTermNum i k s) (substTermNum i k t)
  | .mul s t => .mul (substTermNum i k s) (substTermNum i k t)

/-- Substitute the numeral for `k` in place of the free variable `xᵢ` in a formula. -/
def substNum (i k : ℕ) : AForm → AForm
  | .eq s t => .eq (substTermNum i k s) (substTermNum i k t)
  | .not φ => .not (substNum i k φ)
  | .and φ ψ => .and (substNum i k φ) (substNum i k ψ)
  | .all j φ => if j = i then .all j φ else .all j (substNum i k φ)

theorem evalTerm_substTermNum (i k : ℕ) (t : ATerm) (ρ : ℕ → ℕ) :
    evalTerm (substTermNum i k t) ρ = evalTerm t (Function.update ρ i k) := by
  induction t with
  | var j =>
    by_cases h : j = i <;> simp [substTermNum, evalTerm, h, Function.update]
  | zero => rfl
  | succ t ih => simp [substTermNum, evalTerm, ih]
  | add s t ihs iht => simp [substTermNum, evalTerm, ihs, iht]
  | mul s t ihs iht => simp [substTermNum, evalTerm, ihs, iht]

theorem Sat_substNum (i k : ℕ) (φ : AForm) (ρ : ℕ → ℕ) :
    Sat (substNum i k φ) ρ ↔ Sat φ (Function.update ρ i k) := by
  induction φ generalizing ρ with
  | eq s t => simp [substNum, evalTerm_substTermNum]
  | not φ ih => simp [substNum, ih]
  | and φ ψ ihφ ihψ => simp [substNum, ihφ, ihψ]
  | all j φ ih =>
    by_cases h : j = i
    · subst h
      have hsub : substNum j k (AForm.all j φ) = AForm.all j φ := by simp [substNum]
      rw [hsub]
      simp only [Sat_all]
      exact forall_congr' fun v => by rw [Function.update_idem]
    · simp only [substNum, if_neg h, Sat_all]
      exact forall_congr' fun v => by rw [ih, Function.update_comm h]

/-! ## Definability in the standard model -/

/-- A set `S ⊆ ℕ` is *arithmetically definable* if some formula of arithmetic defines it,
using `x₀` as its (only) free variable. -/
def Definable1 (S : Set ℕ) : Prop := ∃ φ : AForm, ∀ ρ : ℕ → ℕ, Sat φ ρ ↔ ρ 0 ∈ S

/-- A binary relation on `ℕ` is *arithmetically definable* if some formula of arithmetic
defines it, using `x₀, x₁` as its (only) free variables. -/
def Definable2 (R : ℕ → ℕ → Prop) : Prop := ∃ φ : AForm, ∀ ρ : ℕ → ℕ, Sat φ ρ ↔ R (ρ 0) (ρ 1)

/-- A formula is *true* (in the standard model) if it holds under every assignment; for
sentences this is ordinary truth in `ℕ`. -/
def IsTrue (φ : AForm) : Prop := ∀ ρ : ℕ → ℕ, Sat φ ρ

/-- The set of Gödel numbers of true formulas, w.r.t. a Gödel numbering `code`. -/
def TruthSet (code : AForm → ℕ) : Set ℕ := {n | ∃ φ : AForm, code φ = n ∧ IsTrue φ}

/-! ## Closure properties of definability -/

theorem Definable1.compl {S : Set ℕ} (h : Definable1 S) : Definable1 Sᶜ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨.not φ, by intro ρ; simp [hφ ρ, Set.mem_compl_iff]⟩

/-- Auxiliary: if `φ` defines `S` using the variable `x₀`, then the formula
`∀ x₀, x₀ = x₁ → φ` defines `S` using the variable `x₁`. -/
theorem Sat_shift_to_var_one {S : Set ℕ} {φ : AForm} (hφ : ∀ ρ : ℕ → ℕ, Sat φ ρ ↔ ρ 0 ∈ S)
    (ρ : ℕ → ℕ) :
    Sat (.all 0 (.not (.and (.eq (.var 0) (.var 1)) (.not φ)))) ρ ↔ ρ 1 ∈ S := by
  have key : ∀ w : ℕ, Sat φ (Function.update ρ 0 w) ↔ w ∈ S := by
    intro w; rw [hφ]; simp
  simp only [Sat_all, Sat_not, Sat_and, Sat_eq, evalTerm]
  constructor
  · intro h
    by_contra hmem
    exact h (ρ 1) ⟨by simp, fun hs => hmem ((key _).mp hs)⟩
  · rintro hmem w ⟨hw, hns⟩
    simp only [Function.update_self] at hw
    rw [show Function.update ρ 0 w 1 = ρ 1 by simp] at hw
    exact hns ((key w).mpr (hw ▸ hmem))

theorem Definable1.preimage {S : Set ℕ} {f : ℕ → ℕ} (hS : Definable1 S)
    (hf : Definable2 fun x y => y = f x) : Definable1 (f ⁻¹' S) := by
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨θ, hθ⟩ := hf
  -- `∀ x₁, θ(x₀,x₁) → (∀ x₀, x₀ = x₁ → φ(x₀))`
  refine ⟨.all 1 (.not (.and θ (.not (.all 0 (.not (.and (.eq (.var 0) (.var 1)) (.not φ))))))), ?_⟩
  intro ρ
  have hin : ∀ v : ℕ, Sat (.all 0 (.not (.and (.eq (.var 0) (.var 1)) (.not φ))))
      (Function.update ρ 1 v) ↔ v ∈ S := by
    intro v
    rw [Sat_shift_to_var_one hφ]
    simp
  have hth : ∀ v : ℕ, Sat θ (Function.update ρ 1 v) ↔ v = f (ρ 0) := by
    intro v
    rw [hθ]
    simp
  simp only [Sat_all, Sat_not, Sat_and, Set.mem_preimage]
  constructor
  · intro h
    by_contra hmem
    exact h (f (ρ 0)) ⟨(hth _).mpr rfl, fun hs => hmem ((hin _).mp hs)⟩
  · rintro hmem v ⟨hv, hns⟩
    exact hns ((hin v).mpr (((hth v).mp hv) ▸ hmem))

/-- The diagonal of a definable binary relation is definable. -/
theorem Definable2.diagonal {R : ℕ → ℕ → Prop} (hR : Definable2 R) :
    Definable1 {n | R n n} := by
  obtain ⟨θ, hθ⟩ := hR
  -- `∀ x₁, x₁ = x₀ → θ(x₀,x₁)`
  refine ⟨.all 1 (.not (.and (.eq (.var 1) (.var 0)) (.not θ))), ?_⟩
  intro ρ
  have hth : ∀ v : ℕ, Sat θ (Function.update ρ 1 v) ↔ R (ρ 0) v := by
    intro v
    rw [hθ]
    simp
  simp only [Sat_all, Sat_not, Sat_and, Sat_eq, evalTerm, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hmem
    refine h (ρ 0) ⟨by simp, fun hs => hmem ?_⟩
    exact (hth _).mp hs
  · rintro hmem v ⟨hv, hns⟩
    simp only [Function.update_self, show Function.update ρ 1 v 0 = ρ 0 by simp] at hv
    exact hns ((hth v).mpr (hv ▸ hmem))

/-! ## Tarski's undefinability theorem -/

/-- **Undefinability of satisfaction.**  No arithmetically definable binary relation is
universal for the arithmetically definable sets: for *every* Gödel numbering (indeed, for
every indexing whatsoever) of the definable sets by numbers, the satisfaction relation
`{(e, m) | m ∈ Sₑ}` fails to be arithmetically definable. -/
theorem no_universal_definable_relation (R : ℕ → ℕ → Prop) (hR : Definable2 R)
    (huniv : ∀ S : Set ℕ, Definable1 S → ∃ e : ℕ, ∀ m : ℕ, m ∈ S ↔ R e m) : False := by
  obtain ⟨e, he⟩ := huniv {n | R n n}ᶜ hR.diagonal.compl
  have := he e
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at this
  tauto

/-- **Tarski's undefinability theorem.**  Fix any Gödel numbering `code` of the formulas of
arithmetic (an injection into `ℕ`), any enumeration `enum` of the formulas, and diagonal
formulas `diag e` expressing "the `e`-th formula holds of `e`".  If the diagonal function
`e ↦ code (diag e)` is arithmetically definable — as it is for every standard, effective
Gödel numbering — then the set of Gödel numbers of the *true* formulas of arithmetic is not
arithmetically definable.  In short: arithmetical truth is not arithmetically definable. -/
theorem Tarski_undefinability
    (code : AForm → ℕ) (hcode : Function.Injective code)
    (enum : ℕ → AForm) (henum : Function.Surjective enum)
    (diag : ℕ → AForm)
    (hdiag : ∀ (e : ℕ) (ρ : ℕ → ℕ), Sat (diag e) ρ ↔ Sat (enum e) (Function.update ρ 0 e))
    (hdiagdef : Definable2 fun x y => y = code (diag x)) :
    ¬ Definable1 (TruthSet code) := by
  intro hT
  -- `S` is the set of `e` such that the `e`-th diagonal formula is *not* true.
  set S : Set ℕ := (fun e => code (diag e)) ⁻¹' (TruthSet code) with hS
  have hSdef : Definable1 Sᶜ := (hT.preimage hdiagdef).compl
  obtain ⟨χ, hχ⟩ := hSdef
  obtain ⟨e, he⟩ := henum χ
  -- membership in the truth set is exactly truth of the diagonal formula
  have hmem : code (diag e) ∈ TruthSet code ↔ IsTrue (diag e) := by
    constructor
    · rintro ⟨ψ, h1, h2⟩
      exact hcode h1 ▸ h2
    · intro h
      exact ⟨diag e, rfl, h⟩
  -- and truth of the diagonal formula is exactly membership of `e` in `Sᶜ`
  have hdiagtrue : IsTrue (diag e) ↔ e ∈ Sᶜ := by
    constructor
    · intro h
      have := (hχ (Function.update (fun _ => 0) 0 e)).mp
        (he ▸ (hdiag e (fun _ => 0)).mp (h _))
      simpa using this
    · intro h ρ
      rw [hdiag e ρ, he, hχ]
      simpa using h
  have hSe : e ∈ S ↔ code (diag e) ∈ TruthSet code := Iff.rfl
  rw [Set.mem_compl_iff] at hdiagtrue
  rw [hSe, hmem] at hdiagtrue
  tauto

/-! ## The hypotheses are satisfiable: an explicit Gödel numbering -/

open Classical in
/-- An enumeration of all formulas of arithmetic. -/
noncomputable def formEnum (n : ℕ) : AForm := (Encodable.decode (α := AForm) n).getD default

theorem formEnum_surjective : Function.Surjective formEnum :=
  fun φ => ⟨Encodable.encode φ, by simp [formEnum]⟩

/-- The `e`-th diagonal formula: "the `e`-th formula holds of `e`" (tagged with a trivially
true conjunct that makes the assignment `e ↦ diagForm e` injective). -/
noncomputable def diagForm (e : ℕ) : AForm :=
  .and (substNum 0 e (formEnum e)) (.eq (numeral e) (numeral e))

theorem Sat_diagForm (e : ℕ) (ρ : ℕ → ℕ) :
    Sat (diagForm e) ρ ↔ Sat (formEnum e) (Function.update ρ 0 e) := by
  simp [diagForm, Sat_substNum]

theorem diagForm_injective : Function.Injective diagForm := by
  intro e e' h
  simp only [diagForm, AForm.and.injEq, AForm.eq.injEq] at h
  exact numeral_injective h.2.1

open Classical in
/-- An explicit Gödel numbering: diagonal formulas get the odd number `2e + 1`, all other
formulas get an even number. -/
noncomputable def stdCode (φ : AForm) : ℕ :=
  if h : ∃ e, diagForm e = φ then 2 * h.choose + 1 else 2 * Encodable.encode φ

theorem stdCode_diagForm (e : ℕ) : stdCode (diagForm e) = 2 * e + 1 := by
  have h : ∃ e', diagForm e' = diagForm e := ⟨e, rfl⟩
  rw [stdCode, dif_pos h, diagForm_injective h.choose_spec]

theorem stdCode_injective : Function.Injective stdCode := by
  intro φ ψ h
  rw [stdCode, stdCode] at h
  by_cases hφ : ∃ e, diagForm e = φ <;> by_cases hψ : ∃ e, diagForm e = ψ
  · rw [dif_pos hφ, dif_pos hψ] at h
    have : hφ.choose = hψ.choose := by omega
    rw [← hφ.choose_spec, ← hψ.choose_spec, this]
  · rw [dif_pos hφ, dif_neg hψ] at h
    omega
  · rw [dif_neg hφ, dif_pos hψ] at h
    omega
  · rw [dif_neg hφ, dif_neg hψ] at h
    exact Encodable.encode_injective (by omega)

/-- There exists a Gödel numbering satisfying all the hypotheses of
`Tarski_undefinability`; in particular, the theorem is not vacuous. -/
theorem exists_goedel_numbering_with_undefinable_truth :
    ∃ (code : AForm → ℕ) (enum : ℕ → AForm) (diag : ℕ → AForm),
      Function.Injective code ∧ Function.Surjective enum ∧
      (∀ (e : ℕ) (ρ : ℕ → ℕ), Sat (diag e) ρ ↔ Sat (enum e) (Function.update ρ 0 e)) ∧
      (Definable2 fun x y => y = code (diag x)) ∧
      ¬ Definable1 (TruthSet code) := by
  have hdiagdef : Definable2 fun x y => y = stdCode (diagForm x) := by
    refine ⟨.eq (.var 1) (.succ (.add (.var 0) (.var 0))), fun ρ => ?_⟩
    simp only [Sat_eq, evalTerm, stdCode_diagForm]
    omega
  exact ⟨stdCode, formEnum, diagForm, stdCode_injective, formEnum_surjective, Sat_diagForm,
    hdiagdef,
    Tarski_undefinability stdCode stdCode_injective formEnum formEnum_surjective diagForm
      Sat_diagForm hdiagdef⟩

/-! ## Sanity checks: the framework is non-degenerate -/

/-- The set of even numbers is arithmetically definable, so `Definable1` is not empty. -/
theorem definable1_even : Definable1 {n : ℕ | ∃ k, n = k + k} := by
  refine ⟨.not (.all 1 (.not (.eq (.var 0) (.add (.var 1) (.var 1))))), fun ρ => ?_⟩
  simp only [Sat_not, Sat_all, Sat_eq, evalTerm, Set.mem_setOf_eq, not_forall, not_not]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa using hk⟩

/-- Truth is non-degenerate: `0 = 0` is true and `¬(0 = 0)` is not. -/
theorem isTrue_zero_eq_zero : IsTrue (.eq .zero .zero) := fun _ => rfl

theorem not_isTrue_not_zero_eq_zero : ¬ IsTrue (.not (.eq .zero .zero)) := by
  intro h
  exact h (fun _ => 0) rfl

/-- The truth set of the explicit Gödel numbering is a proper nonempty subset of `ℕ`. -/
theorem truthSet_nontrivial :
    stdCode (.eq .zero .zero) ∈ TruthSet stdCode ∧
      stdCode (.not (.eq .zero .zero)) ∉ TruthSet stdCode := by
  refine ⟨⟨_, rfl, isTrue_zero_eq_zero⟩, ?_⟩
  rintro ⟨ψ, h1, h2⟩
  exact not_isTrue_not_zero_eq_zero (stdCode_injective h1 ▸ h2)

end Frontier

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

