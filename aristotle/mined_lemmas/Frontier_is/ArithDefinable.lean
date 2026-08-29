import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

def ArithDefinable (S : Nat → Prop) : Prop :=
  ∃ φ : AForm, ∀ v : Nat → Nat, (φ.Sat v ↔ S (v 0))

/-- A binary relation on `Nat` is *arithmetically definable* if some arithmetical formula `φ`
is satisfied exactly by those assignments whose values at `x₀` and `x₁` are related.  Again,
quantifying over all assignments forces `φ` to have no free variables besides `x₀, x₁`. -/
