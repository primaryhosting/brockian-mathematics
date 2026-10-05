/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is given as a plain block comment and repeated below verbatim.)

import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open FirstOrder Language

/-! ## The language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, the successor `S`,
addition and multiplication. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | succ : arithFunc 1
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The relation symbols of the language of arithmetic: the order relation `<`. -/
inductive arithRel : ℕ → Type
  | lt : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic, `(0, S, +, ·, <)`. -/
def arith : Language where
  Functions := arithFunc
  Relations := arithRel

/-- The standard model of arithmetic: the natural numbers, with the usual
interpretation of `0`, `S`, `+`, `·` and `<`. -/
instance : arith.Structure ℕ where
  funMap {n} f := match n, f with
    | _, .zero => fun _ => 0
    | _, .succ => fun v => v 0 + 1
    | _, .add => fun v => v 0 + v 1
    | _, .mul => fun v => v 0 * v 1
  RelMap {n} r := match n, r with
    | _, .lt => fun v => v 0 < v 1

/-- The numeral `S(S(...S(0)...))` (with `n` successors) as a term of the language
of arithmetic. -/
def numeral {α : Type} : ℕ → arith.Term α
  | 0 => Term.func arithFunc.zero (fun i => i.elim0)
  | n + 1 => Term.func arithFunc.succ (fun _ => numeral n)

@[simp] theorem funMap_zero (v : Fin 0 → ℕ) :
    Structure.funMap (L := arith) (M := ℕ) arithFunc.zero v = 0 := rfl

@[simp] theorem funMap_succ (v : Fin 1 → ℕ) :
    Structure.funMap (L := arith) (M := ℕ) arithFunc.succ v = v 0 + 1 := rfl

@[simp] theorem funMap_add (v : Fin 2 → ℕ) :
    Structure.funMap (L := arith) (M := ℕ) arithFunc.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_mul (v : Fin 2 → ℕ) :
    Structure.funMap (L := arith) (M := ℕ) arithFunc.mul v = v 0 * v 1 := rfl

@[simp] theorem relMap_lt (v : Fin 2 → ℕ) :
    Structure.RelMap (L := arith) (M := ℕ) arithRel.lt v ↔ v 0 < v 1 := Iff.rfl

@[simp]
theorem realize_numeral {α : Type} (v : α → ℕ) (n : ℕ) :
    Term.realize v (numeral n : arith.Term α) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [numeral] using ih

/-! ## Arithmetical sets and relations -/

/-- A set of natural numbers is **arithmetical** (i.e. *arithmetically definable*) when it is
the extension, in the standard model `ℕ`, of a first-order formula of the language of
arithmetic with one free variable. -/
def IsArithmetical (A : Set ℕ) : Prop :=
  ∃ φ : arith.Formula (Fin 1), ∀ n : ℕ, n ∈ A ↔ φ.Realize ![n]

/-- A binary relation on the natural numbers is **arithmetical** when it is the extension,
in the standard model `ℕ`, of a first-order formula of the language of arithmetic with two
free variables. -/
def IsArithmetical₂ (R : Set (ℕ × ℕ)) : Prop :=
  ∃ φ : arith.Formula (Fin 2), ∀ m n : ℕ, (m, n) ∈ R ↔ φ.Realize ![m, n]

/-! ## Tarski's undefinability theorem -/

/-- Diagonalising a binary formula: `diagonal θ` is the formula in one free variable
`¬ θ(x, x)`. -/
def diagonal (θ : arith.Formula (Fin 2)) : arith.Formula (Fin 1) :=
  (θ.relabel (fun _ => 0)).not

@[simp]
theorem realize_diagonal (θ : arith.Formula (Fin 2)) (n : ℕ) :
    (diagonal θ).Realize ![n] ↔ ¬ θ.Realize ![n, n] := by
  have h : (![n] : Fin 1 → ℕ) ∘ (fun _ => (0 : Fin 1)) = ![n, n] := by
    funext i; fin_cases i <;> rfl
  simp [diagonal, Formula.realize_relabel, h]

/--
**Tarski's undefinability theorem.**

Fix any Gödel numbering `code` of the arithmetical formulas in one free variable.
Then the satisfaction relation for these formulas over the standard model of arithmetic
is not itself arithmetically definable: there is no set `Sat ⊆ ℕ × ℕ` which both

* correctly expresses satisfaction, i.e. `(⌜phi⌝, n) ∈ Sat ↔ ℕ ⊨ phi(n)`, and
* is arithmetical.
-/
theorem Tarski_undefinability
    (code : arith.Formula (Fin 1) → ℕ) (Sat : Set (ℕ × ℕ))
    (hSat : ∀ (φ : arith.Formula (Fin 1)) (n : ℕ), (code φ, n) ∈ Sat ↔ φ.Realize ![n]) :
    ¬ IsArithmetical₂ Sat := by
  rintro ⟨θ, hθ⟩
  set a : ℕ := code (diagonal θ) with ha
  have h1 : (a, a) ∈ Sat ↔ (diagonal θ).Realize ![a] := hSat (diagonal θ) a
  have h2 : (a, a) ∈ Sat ↔ θ.Realize ![a, a] := hθ a a
  rw [realize_diagonal] at h1
  tauto

/-! ## Non-vacuity: satisfaction sets exist -/

/-- The genuine satisfaction relation attached to a Gödel numbering `code`:
`(m, n)` belongs to it iff `m` is the code of some formula `φ` with `ℕ ⊨ φ(n)`. -/
def satSet (code : arith.Formula (Fin 1) → ℕ) : Set (ℕ × ℕ) :=
  {p | ∃ φ : arith.Formula (Fin 1), code φ = p.1 ∧ φ.Realize ![p.2]}

/-- For an injective Gödel numbering, `satSet code` really does express satisfaction; in
particular the hypothesis of `Tarski_undefinability` is not vacuous. -/
theorem mem_satSet (code : arith.Formula (Fin 1) → ℕ) (hcode : Function.Injective code)
    (φ : arith.Formula (Fin 1)) (n : ℕ) :
    (code φ, n) ∈ satSet code ↔ φ.Realize ![n] := by
  constructor
  · rintro ⟨ψ, h, hψ⟩
    exact hcode h ▸ hψ
  · intro h
    exact ⟨φ, rfl, h⟩

/-- **Tarski's undefinability theorem, concrete form.** For any injective Gödel numbering of
the formulas in one free variable, the corresponding satisfaction relation over the standard
model of arithmetic is not arithmetical. -/
theorem Tarski_undefinability_satSet (code : arith.Formula (Fin 1) → ℕ)
    (hcode : Function.Injective code) : ¬ IsArithmetical₂ (satSet code) :=
  Tarski_undefinability code (satSet code) (mem_satSet code hcode)

/-- **Tarski's undefinability theorem, "no universal formula" form.** No single formula
`θ(x, y)` of the language of arithmetic is universal for the formulas in one free variable:
there is always a formula `φ` such that no value of the parameter `x` makes `θ(x, ·)` define
the same set as `φ`. -/
theorem Tarski_no_universal_formula :
    ¬ ∃ θ : arith.Formula (Fin 2), ∀ φ : arith.Formula (Fin 1), ∃ e : ℕ,
      ∀ n : ℕ, (θ.Realize ![e, n] ↔ φ.Realize ![n]) := by
  rintro ⟨θ, hθ⟩
  obtain ⟨e, he⟩ := hθ (diagonal θ)
  have := he e
  rw [realize_diagonal] at this
  tauto

/-! ## Truth of sentences -/

/-- A ternary relation on the natural numbers is **arithmetical** when it is the extension,
in the standard model `ℕ`, of a first-order formula of the language of arithmetic with three
free variables. -/
def IsArithmetical₃ (S : Set (ℕ × ℕ × ℕ)) : Prop :=
  ∃ φ : arith.Formula (Fin 3), ∀ a b c : ℕ, (a, b, c) ∈ S ↔ φ.Realize ![a, b, c]

/-- Arithmetical relations are closed under the combination
`{(m, n) | ∃ k, (m, n, k) ∈ S ∧ k ∈ A}`. -/
theorem isArithmetical₂_exists_and {S : Set (ℕ × ℕ × ℕ)} {A : Set ℕ}
    (hS : IsArithmetical₃ S) (hA : IsArithmetical A) :
    IsArithmetical₂ {p : ℕ × ℕ | ∃ k : ℕ, (p.1, p.2, k) ∈ S ∧ k ∈ A} := by
  obtain ⟨σ, hσ⟩ := hS
  obtain ⟨α, hα⟩ := hA
  classical
  set g : Fin 3 → Fin 2 ⊕ Unit := ![Sum.inl 0, Sum.inl 1, Sum.inr ()] with hg
  set h : Fin 1 → Fin 2 ⊕ Unit := ![Sum.inr ()] with hh
  refine ⟨Formula.iExs Unit ((σ.relabel g) ⊓ (α.relabel h)), ?_⟩
  intro m n
  rw [Formula.realize_iExs]
  simp only [Set.mem_setOf_eq, BoundedFormula.realize_inf, Formula.realize_relabel]
  constructor
  · rintro ⟨k, hk, hkA⟩
    refine ⟨fun _ => k, ?_, ?_⟩
    · have : (Sum.elim ![m, n] (fun _ : Unit => k)) ∘ g = ![m, n, k] := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact (hσ m n k).1 hk
    · have : (Sum.elim ![m, n] (fun _ : Unit => k)) ∘ h = ![k] := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact (hα k).1 hkA
  · rintro ⟨i, h1, h2⟩
    refine ⟨i (), ?_, ?_⟩
    · have e : (Sum.elim ![m, n] i) ∘ g = ![m, n, i ()] := by
        funext j; fin_cases j <;> rfl
      rw [e] at h1
      exact (hσ m n (i ())).2 h1
    · have e : (Sum.elim ![m, n] i) ∘ h = ![i ()] := by
        funext j; fin_cases j <;> rfl
      rw [e] at h2
      exact (hα (i ())).2 h2

/-- Substituting the numeral for `n` for the unique free variable of `φ`, producing a
sentence of the language of arithmetic. -/
def substNumeral (φ : arith.Formula (Fin 1)) (n : ℕ) : arith.Sentence :=
  φ.subst (fun _ => numeral n)

theorem realize_substNumeral (φ : arith.Formula (Fin 1)) (n : ℕ) :
    (ℕ ⊨ substNumeral φ n) ↔ φ.Realize ![n] := by
  rw [Sentence.Realize, substNumeral, Formula.realize_subst]
  have : (fun a : Fin 1 => Term.realize (default : Empty → ℕ) (numeral n : arith.Term Empty))
      = ![n] := by
    funext i; fin_cases i; simp
  rw [this]

/--
**Tarski's undefinability theorem for the set of true sentences.**

Suppose we are given Gödel numberings `codeF` of the formulas in one free variable and
`codeS` of the sentences, together with a substitution function `sub` computing the code of
`φ(n̄)` from the code of `φ` and the number `n`, and suppose (as holds for every reasonable
coding) that the graph of `sub` is arithmetical.

Then the set of (codes of) true sentences of arithmetic is not arithmetical: arithmetical
truth is not arithmetically definable.
-/
theorem Tarski_undefinability_truth_set
    (codeF : arith.Formula (Fin 1) → ℕ) (codeS : arith.Sentence → ℕ) (sub : ℕ → ℕ → ℕ)
    (hsub : ∀ (φ : arith.Formula (Fin 1)) (n : ℕ), sub (codeF φ) n = codeS (substNumeral φ n))
    (hsubDef : IsArithmetical₃ {t : ℕ × ℕ × ℕ | sub t.1 t.2.1 = t.2.2})
    (T : Set ℕ) (hT : ∀ σ : arith.Sentence, codeS σ ∈ T ↔ (ℕ ⊨ σ)) :
    ¬ IsArithmetical T := by
  intro hTdef
  refine Tarski_undefinability codeF
    {p : ℕ × ℕ | ∃ k : ℕ, (p.1, p.2, k) ∈ {t : ℕ × ℕ × ℕ | sub t.1 t.2.1 = t.2.2} ∧ k ∈ T}
    ?_ (isArithmetical₂_exists_and hsubDef hTdef)
  intro φ n
  constructor
  · rintro ⟨k, hk, hkT⟩
    simp only [Set.mem_setOf_eq] at hk
    rw [← hk, hsub φ n] at hkT
    exact (realize_substNumeral φ n).1 ((hT _).1 hkT)
  · intro h
    refine ⟨sub (codeF φ) n, rfl, ?_⟩
    rw [hsub φ n]
    exact (hT _).2 ((realize_substNumeral φ n).2 h)

end Frontier

