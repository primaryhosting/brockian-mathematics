/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (This development is self-contained pure Lean 4; it needs no Mathlib lemmas, so that the
-- module docstring required by the task specification can be the very first item of the file.)

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

namespace Frontier

/-!
## An abstract provability framework

Gödel's second incompleteness theorem says that no consistent, recursively axiomatized
theory `T` extending `PA` proves the sentence `Con(T)` expressing its own consistency.

The whole arithmetical content of that statement is encapsulated by the
Hilbert–Bernays–Löb *derivability conditions* for the provability predicate
`Prov_T` (arithmetized by a `Σ₁` formula `□`), together with the *diagonal lemma*,
which produces a Gödel sentence `g` with `T ⊢ g ↔ ¬□g`.  Both of these hold for every
consistent recursively axiomatized `T ⊇ PA`.

Below we axiomatize exactly this situation: a set of sentences with implication, falsity,
a provability operator `box`, a deductive closure operator `Prov` closed under modus ponens
and containing the two Hilbert axiom schemes for the implicational fragment, and the three
derivability conditions.  Consistency of the theory is `¬ Prov bot`, and the sentence
`con = □⊥ → ⊥` is the formalized consistency statement.

The main theorem `Frontier.Goedel_second_incompleteness` then states and proves:
if such a theory is consistent and has a Gödel sentence, it does not prove its own
consistency statement.  This is a fully Lean-checked reduction of the second incompleteness
theorem to the derivability conditions and the diagonal lemma.

The example `Frontier.ProvabilityFramework.exists_consistent_with_goedelSentence` at the end
of the file shows that the hypotheses of the main theorem are jointly satisfiable, i.e. that
the theorem is not vacuous.
-/

/-- An abstract framework for provability: a type of sentences carrying an implication,
a falsity constant, an internal provability operator `box`, and a predicate `Prov`
("the theory proves") closed under modus ponens, containing the Hilbert axiom schemes
`K` and `S`, and satisfying the three Hilbert–Bernays–Löb derivability conditions. -/
structure ProvabilityFramework where
  /-- The type of sentences of the theory. -/
  Sent : Type
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- The false sentence. -/
  bot : Sent
  /-- The internal provability operator: `box p` expresses "`p` is provable in the theory". -/
  box : Sent → Sent
  /-- `Prov p` means: the theory proves the sentence `p`. -/
  Prov : Sent → Prop
  /-- Hilbert axiom scheme `K`. -/
  ax_K : ∀ p q : Sent, Prov (imp p (imp q p))
  /-- Hilbert axiom scheme `S`. -/
  ax_S : ∀ p q r : Sent,
    Prov (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Modus ponens. -/
  mp : ∀ {p q : Sent}, Prov (imp p q) → Prov p → Prov q
  /-- First derivability condition: provable sentences are provably provable. -/
  D1 : ∀ p : Sent, Prov p → Prov (box p)
  /-- Second derivability condition: the theory internalizes modus ponens. -/
  D2 : ∀ p q : Sent, Prov (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: the theory internalizes the first one. -/
  D3 : ∀ p : Sent, Prov (imp (box p) (box (box p)))

namespace ProvabilityFramework

variable (F : ProvabilityFramework)

/-- The theory is consistent when it does not prove falsity. -/
def Consistent : Prop := ¬ F.Prov F.bot

/-- The internal consistency statement `Con(T) = □⊥ → ⊥`. -/
def con : F.Sent := F.imp (F.box F.bot) F.bot

/-- `g` is a Gödel sentence when the theory proves `g ↔ ¬□g`
(stated as the two implications, `¬p` being `p → ⊥`). -/
def IsGoedelSentence (g : F.Sent) : Prop :=
  F.Prov (F.imp g (F.imp (F.box g) F.bot)) ∧
    F.Prov (F.imp (F.imp (F.box g) F.bot) g)

/-! ### Basic propositional derivations inside the theory -/

variable {F}

/-- The derived rule: from `⊢ a → (b → c)` and `⊢ a → b` infer `⊢ a → c`. -/
theorem prov_imp_dist {a b c : F.Sent} (h₁ : F.Prov (F.imp a (F.imp b c)))
    (h₂ : F.Prov (F.imp a b)) : F.Prov (F.imp a c) :=
  F.mp (F.mp (F.ax_S a b c) h₁) h₂

/-- Weakening: from `⊢ b` infer `⊢ a → b`. -/
theorem prov_weaken {a b : F.Sent} (h : F.Prov b) : F.Prov (F.imp a b) :=
  F.mp (F.ax_K b a) h

/-- Transitivity of implication. -/
theorem prov_imp_trans {a b c : F.Sent} (h₁ : F.Prov (F.imp a b))
    (h₂ : F.Prov (F.imp b c)) : F.Prov (F.imp a c) :=
  prov_imp_dist (prov_weaken h₂) h₁

/-- Contraposition-style rule: from `⊢ a → b` infer `⊢ (b → c) → (a → c)`. -/
theorem prov_imp_mono {a b c : F.Sent} (h : F.Prov (F.imp a b)) :
    F.Prov (F.imp (F.imp b c) (F.imp a c)) :=
  prov_imp_dist
    (prov_imp_trans (F.ax_K (F.imp b c) a) (F.ax_S a b c))
    (prov_weaken h)

/-! ### The key intermediate lemmas -/

/-- **Key lemma (formalized Löb-style step).**  For a Gödel sentence `g`, the theory
proves `□g → □⊥`: if `g` were provable, then provably `¬□g` would be provable, and hence
`⊥` would be provable. -/
theorem prov_box_imp_box_bot {g : F.Sent} (hg : F.IsGoedelSentence g) :
    F.Prov (F.imp (F.box g) (F.box F.bot)) := by
  -- `⊢ □g → □(□g → ⊥)`
  have h₁ : F.Prov (F.imp (F.box g) (F.box (F.imp (F.box g) F.bot))) :=
    F.mp (F.D2 g (F.imp (F.box g) F.bot)) (F.D1 _ hg.1)
  -- `⊢ □(□g → ⊥) → (□□g → □⊥)`
  have h₂ : F.Prov (F.imp (F.box (F.imp (F.box g) F.bot))
      (F.imp (F.box (F.box g)) (F.box F.bot))) := F.D2 (F.box g) F.bot
  -- `⊢ □g → (□□g → □⊥)`
  have h₃ : F.Prov (F.imp (F.box g) (F.imp (F.box (F.box g)) (F.box F.bot))) :=
    prov_imp_trans h₁ h₂
  -- combine with the third derivability condition `⊢ □g → □□g`
  exact prov_imp_dist h₃ (F.D3 g)

/-- **Key lemma.**  The theory proves that its own consistency implies the Gödel
sentence: `⊢ Con(T) → g`. -/
theorem prov_con_imp_goedelSentence {g : F.Sent} (hg : F.IsGoedelSentence g) :
    F.Prov (F.imp F.con g) :=
  prov_imp_trans (prov_imp_mono (prov_box_imp_box_bot hg)) hg.2

/-- **Gödel's first incompleteness theorem** (the half we need): a consistent theory
does not prove its Gödel sentence. -/
theorem not_prov_goedelSentence {g : F.Sent} (hg : F.IsGoedelSentence g)
    (hcon : F.Consistent) : ¬ F.Prov g := by
  intro hp
  exact hcon (F.mp (F.mp hg.1 hp) (F.D1 g hp))

end ProvabilityFramework

/-- **Gödel's second incompleteness theorem** (Lean-checked reduction to the
Hilbert–Bernays–Löb derivability conditions and the diagonal lemma).

No consistent theory satisfying the derivability conditions — in particular, no consistent
recursively axiomatized theory extending `PA`, for which the derivability conditions and the
diagonal lemma are available — proves its own consistency statement `Con(T) = □⊥ → ⊥`. -/
theorem Goedel_second_incompleteness (F : ProvabilityFramework)
    (hdiag : ∃ g : F.Sent, F.IsGoedelSentence g) (hcon : F.Consistent) :
    ¬ F.Prov F.con := by
  obtain ⟨g, hg⟩ := hdiag
  intro hp
  exact F.not_prov_goedelSentence hg hcon (F.mp (F.prov_con_imp_goedelSentence hg) hp)

namespace ProvabilityFramework

/-- The hypotheses of `Frontier.Goedel_second_incompleteness` are jointly satisfiable:
there is a consistent provability framework possessing a Gödel sentence.  (Here sentences
are propositions, `Prov` is truth, and `box` is the trivial operator; the Gödel sentence
is `False`.)  In particular the main theorem is not vacuous. -/
theorem exists_consistent_with_goedelSentence :
    ∃ F : ProvabilityFramework, F.Consistent ∧ ∃ g : F.Sent, F.IsGoedelSentence g := by
  refine ⟨{ Sent := Prop
            imp := fun p q => p → q
            bot := False
            box := fun _ => True
            Prov := fun p => p
            ax_K := fun _ _ => fun hp _ => hp
            ax_S := fun _ _ _ => fun h₁ h₂ hp => h₁ hp (h₂ hp)
            mp := fun h₁ h₂ => h₁ h₂
            D1 := fun _ _ => trivial
            D2 := fun _ _ => fun _ _ => trivial
            D3 := fun _ => fun _ => trivial }, ?_, False, ?_, ?_⟩
  · intro h
    exact h
  · intro h
    exact h.elim
  · intro h
    exact h trivial

end ProvabilityFramework

end Frontier

