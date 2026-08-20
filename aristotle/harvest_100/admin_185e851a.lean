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
def ip1 (u w : Qubit) : ℂ := ∑ i, (starRingEnd ℂ) (u i) * w i

/-- Hermitian inner product on two-qubit vectors. -/
def ip (φ ψ : TwoQubit) : ℂ := ∑ i, ∑ j, (starRingEnd ℂ) (φ i j) * ψ i j

/-- Squared norm of a two-qubit vector. -/
def nsq (φ : TwoQubit) : ℝ := ∑ i, ∑ j, Complex.normSq (φ i j)

/-- Product (unentangled) vector `u ⊗ v`. -/
def tens (u v : Qubit) : TwoQubit := fun i j => u i * v j

/-- Born rule probability of finding the (not necessarily normalised) state `ψ`
in the direction of the (not necessarily normalised) vector `φ`. -/
def prob (φ ψ : TwoQubit) : ℝ := Complex.normSq (ip φ ψ) / (nsq φ * nsq ψ)

/-- The Hardy state `|ψ⟩ ∝ |00⟩ + |01⟩ + |10⟩`. -/
def psi : TwoQubit := ![![1, 1], ![1, 0]]

/-- Outcome vector for `a₁ = yes` (and for `b₁ = yes`): `|1⟩`. -/
def e1 : Qubit := ![0, 1]

/-- Outcome vector for `a₁ = no` (and for `b₁ = no`): `|0⟩`. -/
def e0 : Qubit := ![1, 0]

/-- Outcome vector for `a₂ = yes` (and for `b₂ = yes`): `|0⟩ - |1⟩`. -/
def f : Qubit := ![1, -1]

section Computations

/-- `|0⟩` and `|1⟩` are orthogonal: the two outcomes of the first measurement are
represented by orthogonal directions. -/
lemma ip1_e0_e1 : ip1 e0 e1 = 0 := by
  simp [ip1, e0, e1]

lemma nsq_psi : nsq psi = 3 := by
  simp [nsq, psi, Complex.normSq_apply]
  norm_num

lemma ip_e1_e1_psi : ip (tens e1 e1) psi = 0 := by
  simp [ip, tens, e1, psi]

lemma ip_f_e0_psi : ip (tens f e0) psi = 0 := by
  simp [ip, tens, f, e0, psi]

lemma ip_e0_f_psi : ip (tens e0 f) psi = 0 := by
  simp [ip, tens, f, e0, psi]

lemma ip_f_f_psi : ip (tens f f) psi = -1 := by
  simp [ip, tens, f, psi]

lemma nsq_tens_f_f : nsq (tens f f) = 4 := by
  simp [nsq, tens, f, Complex.normSq_apply]
  norm_num

end Computations

/-! ### The quantum predictions -/

/-- (H1) `P(a₁ = yes, b₁ = yes) = 0`. -/
theorem hardy_prob_yes_yes : prob (tens e1 e1) psi = 0 := by
  simp [prob, ip_e1_e1_psi]

/-- (H2) `P(a₂ = yes, b₁ = no) = 0`. -/
theorem hardy_prob_f_no : prob (tens f e0) psi = 0 := by
  simp [prob, ip_f_e0_psi]

/-- (H3) `P(a₁ = no, b₂ = yes) = 0`. -/
theorem hardy_prob_no_f : prob (tens e0 f) psi = 0 := by
  simp [prob, ip_e0_f_psi]

/-- (H4) `P(a₂ = yes, b₂ = yes) = 1/12 > 0`: a nonzero *fraction of the runs*. -/
theorem hardy_prob_f_f : prob (tens f f) psi = 1 / 12 := by
  rw [prob, ip_f_f_psi, nsq_tens_f_f, nsq_psi]
  norm_num [Complex.normSq_apply]

/-! ### Local realism forbids the Hardy event -/

/-- **No local hidden-variable model.**  In any hidden-variable model — a measure
space `(Λ, μ)` on which each observable has a definite outcome, so that
`A₁, A₂, B₁, B₂ ⊆ Λ` are the events "the outcome is yes" — Hardy's three vanishing
probabilities force the fourth probability to vanish as well. -/
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
theorem hardy_paradox :
    (ip1 e0 e1 = 0 ∧
      prob (tens e1 e1) psi = 0 ∧
      prob (tens f e0) psi = 0 ∧
      prob (tens e0 f) psi = 0 ∧
      prob (tens f f) psi = 1 / 12) ∧
    (∀ (Λ : Type) (_ : MeasurableSpace Λ) (μ : Measure Λ) (A₁ A₂ B₁ B₂ : Set Λ),
      μ (A₁ ∩ B₁) = 0 → μ (A₂ \ B₁) = 0 → μ (B₂ \ A₁) = 0 →
        μ (A₂ ∩ B₂) ≠ ENNReal.ofReal (1 / 12)) := by
  refine ⟨⟨ip1_e0_e1, hardy_prob_yes_yes, hardy_prob_f_no, hardy_prob_no_f,
    hardy_prob_f_f⟩, ?_⟩
  intro Λ _ μ A₁ A₂ B₁ B₂ h1 h2 h3
  rw [lhv_hardy_event_null μ A₁ A₂ B₁ B₂ h1 h2 h3]
  refine fun h => ?_
  rw [eq_comm, ENNReal.ofReal_eq_zero] at h
  norm_num at h

end

end QI

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

