/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## The syntactic setting

We work with the standard abstract (Hilbert–Bernays–Löb) formulation of Gödel's second
incompleteness theorem.

`Fml` is a language of sentences built from atoms, falsum and implication, together with a
unary operator `box`.  For a recursively axiomatized theory `T` extending `PA`, one reads
`Fml` as (a fragment of) the sentences of arithmetic and `box p` as the arithmetized
provability sentence `Prov_T(⌜p⌝)`; the fact that `T` is recursively axiomatized and extends
`PA` is exactly what supplies the three Löb derivability conditions `D1`, `D2`, `D3` recorded
in `ProvabilitySystem` below, and the diagonal lemma supplies the Gödel fixed point.
-/

/-- Sentences: propositional atoms, falsum, implication, and a provability operator `box`. -/
inductive Fml where
  | atom : Nat → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬ p := p → ⊥`. -/

theorem ProvabilitySystem.box_goedel_imp_box_bot (T : ProvabilitySystem) {G : Fml}
    (hG : T.GoedelSentence G) :
    T.Thm (Fml.imp (Fml.box G) (Fml.box Fml.bot)) := by
  -- From `T ⊢ G → (□G → ⊥)` we get `T ⊢ □(G → (□G → ⊥))`.
  have h1 : T.Thm (Fml.box (Fml.imp G (Fml.imp (Fml.box G) Fml.bot))) := T.D1 hG.forward
  -- Hence `T ⊢ □G → □(□G → ⊥)`.
  have h2 : T.Thm (Fml.imp (Fml.box G) (Fml.box (Fml.imp (Fml.box G) Fml.bot))) :=
    T.mp (T.D2 G (Fml.imp (Fml.box G) Fml.bot)) h1
  -- And `T ⊢ □(□G → ⊥) → (□□G → □⊥)`.
  have h3 : T.Thm (Fml.imp (Fml.box (Fml.imp (Fml.box G) Fml.bot))
      (Fml.imp (Fml.box (Fml.box G)) (Fml.box Fml.bot))) := T.D2 (Fml.box G) Fml.bot
  -- So `T ⊢ □G → (□□G → □⊥)`.
  have h4 : T.Thm (Fml.imp (Fml.box G) (Fml.imp (Fml.box (Fml.box G)) (Fml.box Fml.bot))) :=
    T.syll h2 h3
  -- D3 gives `T ⊢ □G → □□G`, and contraction finishes.
  exact T.contract h4 (T.D3 G)

/--
**Gödel's second incompleteness theorem.**

No consistent recursively axiomatized theory extending `PA` proves its own consistency:
for any provability system `T` satisfying the Löb derivability conditions and possessing a
Gödel fixed point `G` (both of which are supplied by recursive axiomatizability together
with extension of `PA`), if `T` is consistent then `T` does not prove the sentence
`Con(T) = ¬ Prov(⌜⊥⌝)`.
-/
