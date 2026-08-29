import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

def ArithTruth (code : AForm → Nat) (m n : Nat) : Prop :=
  ∃ φ : AForm, code φ = m ∧ φ.Sat (fun _ => n)

/-! ## Tarski's undefinability theorem

The argument is Tarski's diagonal argument.  Given a putative truth formula one forms the
formula `¬ T(x₀, x₀)` and evaluates it at its own Gödel number.
-/

/-- Substituting `x₀` for `x₁` semantically, without any syntactic substitution:
`∃ x₁, (x₀ = x₁ ∧ T)` expresses `T(x₀, x₀)`. -/
