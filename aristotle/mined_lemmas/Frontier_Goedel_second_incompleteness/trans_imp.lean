/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The statement "no consistent recursively axiomatized theory extending `PA` proves its own
consistency" is formalized here in the standard abstract (Hilbert–Bernays–Löb) way.

For a recursively axiomatized theory `T ⊇ PA` one has an arithmetized provability predicate
`Pr_T(⌜·⌝)`, written here as the modality `□`.  The two ingredients supplied by the
arithmetization are:

* the *derivability conditions*: `T ⊢ a → T ⊢ □a` (necessitation), `T ⊢ □(a → b) → (□a → □b)`
  (distribution) and `T ⊢ □a → □□a` (provable Σ₁-completeness);
* the *diagonal lemma*: there is a sentence `G` with `T ⊢ G ↔ ¬□G`.

Both are packaged below: the derivability conditions as the inference system `Prov`, and the
diagonal lemma as an explicit hypothesis `hdiag` of the main theorem.  Everything else — the
implication from consistency of `T` to the unprovability of the consistency statement
`Con_T = ¬□⊥` — is proved here from scratch inside the calculus.

`Prov A` is a *sublogic* of provability in any classical theory `T` whose axiom set is `A`
(all of its axioms and rules are correct for `T ⊢ ·` and `Pr_T`), so the unprovability
conclusion transfers to such theories.
-/

namespace Frontier

/-- Sentences of the language: falsity, implication, and the provability modality `□`. -/
inductive Fml : Type
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬a := a → ⊥`. -/

theorem trans_imp (h₁ : Prov A (imp a b)) (h₂ : Prov A (imp b c)) : Prov A (imp a c) :=
  mp_under (weaken h₂) h₁

end Prov

/-- **Gödel's second incompleteness theorem** (abstract, Hilbert–Bernays–Löb form).

Let `A` be the axiom set of a consistent theory whose provability predicate satisfies the
derivability conditions (built into `Prov`) and for which the diagonal lemma provides a
Gödel sentence `G` with `⊢ G ↔ ¬□G` — this is the case for every consistent recursively
axiomatized theory extending `PA`.  Then the theory does not prove its own consistency
statement `Con = ¬□⊥`. -/
