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

theorem Goedel_second_incompleteness (A : Fml → Prop)
    (hdiag : ∃ G : Fml, Prov A (imp G (Fml.neg (box G))) ∧ Prov A (imp (Fml.neg (box G)) G))
    (hcon : Consistent A) : ¬ Prov A Con := by
  intro hCon
  obtain ⟨G, hG1, hG2⟩ := hdiag
  -- `□G → □(□G → ⊥)`, by necessitating `G → (□G → ⊥)` and distributing.
  have h1 : Prov A (imp (box G) (box (imp (box G) bot))) :=
    (Prov.distrib G (imp (box G) bot)).mp hG1.nec
  -- `□(□G → ⊥) → (□□G → □⊥)`.
  have h2 : Prov A (imp (box (imp (box G) bot)) (imp (box (box G)) (box bot))) :=
    Prov.distrib (box G) bot
  -- Hence `□G → (□□G → □⊥)`.
  have h3 : Prov A (imp (box G) (imp (box (box G)) (box bot))) := Prov.trans_imp h1 h2
  -- With `□G → □□G` this gives `□G → □⊥`.
  have h4 : Prov A (imp (box G) (box bot)) := Prov.mp_under h3 (Prov.four G)
  -- Consistency `□⊥ → ⊥` then yields `¬□G`.
  have h5 : Prov A (Fml.neg (box G)) := Prov.trans_imp h4 hCon
  -- The Gödel sentence is derivable, hence so is `□G`, contradicting `¬□G`.
  have h6 : Prov A G := hG2.mp h5
  exact hcon (h5.mp h6.nec)


/-!
### Non-vacuity

The hypotheses of `Goedel_second_incompleteness` are satisfiable: below we exhibit a consistent
axiom set possessing a fixed point of `¬□·`.  Consistency is checked by the trivial
interpretation in which `□` is read as "true".
-/

/-- The interpretation of formulas in which `□a` is always true.  It validates all axioms and
rules of `Prov`, and is used to certify consistency of concrete axiom sets. -/
