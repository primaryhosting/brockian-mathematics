/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
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

set_option grind.warning false

namespace Frontier

/-! ## CNF formulas -/

/-- A literal: a variable index together with a sign (`true` = positive). -/
abbrev Lit : Type := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause : Type := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- Value of a literal under an assignment. -/

def Language : Type := (n : ℕ) → (Fin n → Bool) → Prop

/-- A certificate that a language is in NP: a polynomial-size family of
straight-line Boolean verifier programs.  Inputs `0, …, n-1` of `prog n` receive
the instance bits, the remaining inputs receive the witness bits. -/
structure NPCert (L : Language) : Type where
  prog : ℕ → List Gate
  bnd : ℕ
  deg : ℕ
  size_le : ∀ n, (prog n).length ≤ bnd * (n + 1) ^ deg
  spec : ∀ (n : ℕ) (x : Fin n → Bool), L n x ↔
    ∃ w : ℕ → Bool,
      evalProg (prog n) (fun i => if h : i < n then x ⟨i, h⟩ else w (i - n)) = true

/-! ### Helper lemmas -/

