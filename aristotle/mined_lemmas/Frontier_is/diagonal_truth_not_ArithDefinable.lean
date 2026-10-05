import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

theorem diagonal_truth_not_ArithDefinable (code : AForm → Nat)
    (hcode : Function.Injective code) :
    ¬ ArithDefinable (fun n => ArithTruth code n n) := by
  intro hdef
  match hdef with
  | ⟨φ, hφ⟩ =>
    -- the "liar" formula `¬ φ(x₀)` and its own Gödel number
    let ψ : AForm := .not φ
    let c : Nat := code ψ
    let v : Nat → Nat := fun _ => c
    have hv0 : v 0 = c := rfl
    have h1 : ψ.Sat v ↔ ¬ ArithTruth code c c := by
      show ¬ φ.Sat v ↔ ¬ ArithTruth code c c
      rw [hφ v, hv0]
    have h2 : ArithTruth code c c ↔ ψ.Sat v := by
      constructor
      · intro hex
        match hex with
        | ⟨χ, hχ, hsat⟩ =>
          have hχψ : χ = ψ := hcode hχ
          exact hχψ ▸ hsat
      · intro h
        exact ⟨ψ, rfl, h⟩
    by_cases hs : ψ.Sat v
    · exact h1.mp hs (h2.mpr hs)
    · exact hs (h2.mp (Classical.byContradiction fun hnT => hs (h1.mpr hnT)))

/-- **Tarski's undefinability theorem** (semantic form).  Let `code` be any injective Gödel
numbering of the formulas of first-order arithmetic.  Then arithmetical truth — the
satisfaction relation `ArithTruth code` of the standard model `Nat` — is *not* arithmetically
definable: there is no arithmetical formula `T(x₀, x₁)` expressing "the arithmetical formula
with Gödel number `x₀` is true of `x₁`". -/
