import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace QI

/-- **Hardy's paradox, deterministic (local hidden variable) form.**

In a local realistic model, each hidden variable `l : Λ` deterministically fixes the outcomes
`a 1 l, a 2 l` of Alice's two possible measurement settings and `b 1 l, b 2 l` of Bob's.
The four Hardy conditions

* some run has `a₁ = b₁ = 1` (this is the positive-probability event),
* never `a₁ = 1` and `b₂ = 1`,
* never `a₂ = 1` and `b₁ = 1`,
* always `a₂ = 1` or `b₂ = 1`,

are jointly contradictory: no local hidden variable assignment can reproduce them. -/

theorem hardy_paradox_deterministic {Λ : Type*} (a₁ a₂ b₁ b₂ : Λ → Bool)
    (hpos : ∃ l, a₁ l = true ∧ b₁ l = true)
    (h₁ : ∀ l, ¬(a₁ l = true ∧ b₂ l = true))
    (h₂ : ∀ l, ¬(a₂ l = true ∧ b₁ l = true))
    (h₃ : ∀ l, a₂ l = true ∨ b₂ l = true) :
    False := by
  obtain ⟨l, ha, hb⟩ := hpos
  rcases h₃ l with h | h
  · exact h₂ l ⟨h, hb⟩
  · exact h₁ l ⟨ha, h⟩

/-- **Hardy's paradox (measure-theoretic / probabilistic form).**

Let `μ` be any measure on a sample space `Ω` (e.g. a probability measure describing the runs of
the experiment), and let `A₁, A₂, B₁, B₂ ⊆ Ω` be the events "Alice's setting `i` yields outcome
`1`" and "Bob's setting `j` yields outcome `1`", as they would be given by a *local realistic*
model where all four outcomes are simultaneously defined on the same sample space.

Hardy's three "zero-probability" conditions

* `μ (A₁ ∩ B₂) = 0`,
* `μ (A₂ ∩ B₁) = 0`,
* `μ (A₂ᶜ ∩ B₂ᶜ) = 0`

force `μ (A₁ ∩ B₁) = 0`. Quantum mechanics, however, predicts a strictly positive fraction of
runs with `A₁ ∩ B₁` (about 9%), so no local realistic model can reproduce the quantum
predictions — a proof of nonlocality without inequalities.

No measurability assumptions are needed: the argument only uses monotonicity and subadditivity
of the outer measure. -/
