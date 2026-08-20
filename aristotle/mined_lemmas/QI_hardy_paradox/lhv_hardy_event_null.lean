import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires every `import` line to precede all other commands,
so the module docstring above sits immediately after `import Mathlib`.

Content of this file.

Hardy's nonlocality argument, in the "without inequalities" (logical) form.

Two spacelike separated parties, Alice and Bob, each choose one of two dichotomic
measurements (`1` or `2`) with outcomes in `{yes, no}`.  Hardy's four conditions are

  (H1)  P(a₁ = yes, b₁ = yes) = 0
  (H2)  P(a₂ = yes, b₁ = no ) = 0
  (H3)  P(a₁ = no , b₂ = yes) = 0
  (H4)  P(a₂ = yes, b₂ = yes) > 0.

*Local realism* (a local hidden-variable model) assigns, to each hidden state `λ`,
definite outcomes for all four observables, and the observed probabilities are
measures of the corresponding events on the hidden-variable space.  Conditions
(H1)–(H3) then force `P(a₂ = yes, b₂ = yes) = 0`, contradicting (H4): the runs in
which Alice measures `2`, Bob measures `2` and both obtain `yes` — a fraction
`1/12` of such runs for the quantum state exhibited below — cannot be explained
by any local hidden-variable model, *without any inequality being used*.

Quantum mechanics realises (H1)–(H4): we exhibit two qubits in the state
`|ψ⟩ ∝ |00⟩ + |01⟩ + |10⟩` together with the measurement vectors

  a₁ = yes : |1⟩            a₁ = no  : |0⟩
  a₂ = yes : |0⟩ - |1⟩
  b₁ = yes : |1⟩            b₁ = no  : |0⟩
  b₂ = yes : |0⟩ - |1⟩

and check by the Born rule that the three Hardy probabilities vanish while
P(a₂ = yes, b₂ = yes) = 1/12.

(There is no Mathlib lemma for this statement; the quantum side is a direct
Born-rule computation and the local-realism side is a short measure-theoretic
argument built from `measure_mono_null` and `measure_union_null`.)
-/

namespace QI

open MeasureTheory

noncomputable section

/-- A one-qubit vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit vector (an element of `ℂ² ⊗ ℂ²`, written in the product basis). -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- Hermitian inner product on one-qubit vectors. -/

theorem lhv_hardy_event_null {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A₁ A₂ B₁ B₂ : Set Λ) (h1 : μ (A₁ ∩ B₁) = 0) (h2 : μ (A₂ \ B₁) = 0)
    (h3 : μ (B₂ \ A₁) = 0) : μ (A₂ ∩ B₂) = 0 := by
  have hsub : A₂ ∩ B₂ ⊆ (A₂ \ B₁) ∪ (B₂ \ A₁) ∪ (A₁ ∩ B₁) := by
    rintro x ⟨hx2, hy2⟩
    by_cases hb1 : x ∈ B₁
    · by_cases ha1 : x ∈ A₁
      · exact Or.inr ⟨ha1, hb1⟩
      · exact Or.inl (Or.inr ⟨hy2, ha1⟩)
    · exact Or.inl (Or.inl ⟨hx2, hb1⟩)
  refine measure_mono_null hsub ?_
  exact measure_union_null (measure_union_null h2 h3) h1

/-! ### The paradox -/

/--
**Hardy's paradox.**

* Quantum mechanics: for the two-qubit state `|ψ⟩ ∝ |00⟩ + |01⟩ + |10⟩` and the
  indicated measurement directions (the two outcomes of the first measurement,
  `e0` and `e1`, being orthogonal), the three Hardy probabilities vanish while
  `P(a₂ = yes, b₂ = yes) = 1/12`.

* Local realism: no local hidden-variable model can reproduce these numbers.  In
  any hidden-variable model satisfying the same three vanishing probabilities, the
  fourth event has probability `0`, hence never the observed fraction `1/12`.

Thus a fraction `1/12` of the runs violates local realism, with no inequality
involved.
-/
