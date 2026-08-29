/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization

Löb's theorem is a statement about the provability predicate `□` (`Bew`, `Pr_PA`) of
Peano Arithmetic:

> if `PA ⊢ (□⌜φ⌝ → φ)` then `PA ⊢ φ`.

Its proof uses exactly two ingredients about `PA` and its provability predicate:

* the **Hilbert–Bernays–Löb derivability conditions**
  * `D1` (necessitation): if `⊢ φ` then `⊢ □φ`;
  * `D2` (distribution):  `⊢ □(φ → ψ) → (□φ → □ψ)`;
  * `D3` (self-awareness): `⊢ □φ → □□φ`;
* the **diagonal (fixed point) lemma**: for every `φ` there is a sentence `ψ` with
  `⊢ ψ ↔ (□ψ → φ)`.

Accordingly we formalize the syntax of the language — classical propositional logic
together with the provability operator `□` — as an inductive type `Frontier.Formula`,
and the derivability relation `Frontier.Provable` as an inductive predicate given by a
Hilbert-style calculus containing modus ponens, the classical propositional axioms and
the three derivability conditions `D1`, `D2`, `D3`.  The diagonal lemma — the only
genuinely arithmetical ingredient, obtained in `PA` from Gödel numbering — is taken as
an explicit hypothesis `diag` of the theorem.

`Frontier.Loeb_theorem` then states precisely: for every formula `φ`, if `⊢ □φ → φ`,
then `⊢ φ`.  The formalized version `Frontier.Loeb_axiom`, i.e. the Gödel–Löb axiom
`⊢ □(□φ → φ) → □φ`, is derived as well.
-/

namespace Frontier

/-- Formulas of the language: classical propositional logic (with falsum `⊥` and
implication `→`) extended by the provability operator `□`. -/
inductive Formula : Type
  /-- An atomic sentence (e.g. the `n`-th sentence of the language of arithmetic). -/
  | atom : ℕ → Formula
  /-- Falsum. -/
  | falsum : Formula
  /-- Implication. -/
  | imp : Formula → Formula → Formula
  /-- The provability operator: `box φ` reads "`φ` is provable in `PA`". -/
  | box : Formula → Formula

@[inherit_doc] scoped infixr:25 " ⇒ " => Formula.imp
@[inherit_doc] scoped prefix:max "□" => Formula.box

/-- Derivability in the theory: a Hilbert-style calculus for classical propositional
logic together with the three Hilbert–Bernays–Löb derivability conditions for the
provability operator `□`. -/
inductive Provable : Formula → Prop
  /-- Modus ponens. -/
  | mp {p q : Formula} : Provable (p ⇒ q) → Provable p → Provable q
  /-- Propositional axiom K. -/
  | ax_k {p q : Formula} : Provable (p ⇒ (q ⇒ p))
  /-- Propositional axiom S. -/
  | ax_s {p q r : Formula} : Provable ((p ⇒ (q ⇒ r)) ⇒ ((p ⇒ q) ⇒ (p ⇒ r)))
  /-- Double negation elimination (classical logic). -/
  | ax_dne {p : Formula} : Provable ((((p ⇒ Formula.falsum) ⇒ Formula.falsum)) ⇒ p)
  /-- `D1`: necessitation — anything provable is provably provable. -/
  | nec {p : Formula} : Provable p → Provable □p
  /-- `D2`: the provability operator distributes over implication. -/
  | dist {p q : Formula} : Provable (□(p ⇒ q) ⇒ (□p ⇒ □q))
  /-- `D3`: provability is provably provable. -/
  | four {p : Formula} : Provable (□p ⇒ □□p)

namespace Provable

/-- `⊢ p → p`. -/

theorem Loeb_axiom (diag : HasDiagonal) (φ : Formula) :
    Provable (□(□φ ⇒ φ) ⇒ □φ) := by
  obtain ⟨ψ, hfwd, hbwd⟩ := diag φ
  have h₁ : Provable (□ψ ⇒ □φ) := box_fixedPoint_imp hfwd
  -- `⊢ (□φ → φ) → (□ψ → φ)`, so `⊢ □(□φ → φ) → □(□ψ → φ)`
  have h₂ : Provable (□(□φ ⇒ φ) ⇒ □(□ψ ⇒ φ)) := box_mono (imp_comp_left h₁)
  -- and `⊢ □(□ψ → φ) → □ψ` since `⊢ (□ψ → φ) → ψ`
  have h₃ : Provable (□(□ψ ⇒ φ) ⇒ □ψ) := box_mono hbwd
  exact imp_trans (imp_trans h₂ h₃) h₁

/-! ### Consistency of the calculus

The calculus above is consistent: it does not prove falsum.  (This is a sanity check
showing that `Frontier.Loeb_theorem` is not a statement about a trivial derivability
predicate.)  We interpret every atom and every boxed formula as `True`; all the axioms
and rules of `Frontier.Provable` are validated by this interpretation, while `falsum`
is not. -/

/-- A trivial interpretation of formulas validating all axioms of the calculus. -/
