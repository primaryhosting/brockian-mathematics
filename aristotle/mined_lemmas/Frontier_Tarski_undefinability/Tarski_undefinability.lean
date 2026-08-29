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
