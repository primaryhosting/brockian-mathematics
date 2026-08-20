/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Statement: A consistent theory cannot prove its own reflection schema for an unprovable sentence (Löb-based).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
Mathlib (as of the pinned revision) contains no development of provability logic,
Gödel's incompleteness theorems, or Löb's theorem: a search for `Loeb`, `Provable`,
`reflection` turns up nothing applicable, so nothing in the library closes or nearly
closes the goal.  We therefore build the standard abstract setting (a theory together
with a provability predicate satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma) from scratch.
-/

namespace Frontier

universe u

/-- An abstract *provability frame*: a type `S` of sentences equipped with

* an implication connective `imp`,
* a falsity constant `bot`,
* an internal provability operator `box` (`box a` is the sentence "`a` is provable"),
* the external predicate `Pr a`, meaning "the theory proves `a`",

subject to the usual closure conditions of a theory containing enough arithmetic:
modus ponens, the propositional laws used below, *ex falso*, the three
Hilbert–Bernays–Löb derivability conditions, and the diagonal (fixed point) lemma. -/
structure ProvabilityFrame (S : Type u) where
  /-- The implication connective. -/
  imp : S → S → S
  /-- The falsity constant. -/
  bot : S
  /-- The internal provability operator: `box a` says "`a` is provable". -/
  box : S → S
  /-- `Pr a` means: the theory proves the sentence `a`. -/
  Pr : S → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b}, Pr (imp a b) → Pr a → Pr b
  /-- Derivability condition D1 (necessitation): what is provable is provably provable. -/
  nec : ∀ {a}, Pr a → Pr (box a)
  /-- Provable implications compose. -/
  imp_trans : ∀ {a b c}, Pr (imp a b) → Pr (imp b c) → Pr (imp a c)
  /-- The propositional law `(a → b → c) → (a → b) → (a → c)`, in rule form. -/
  distrib : ∀ {a b c}, Pr (imp a (imp b c)) → Pr (imp a b) → Pr (imp a c)
  /-- Derivability condition D2: the provability operator distributes over implication. -/
  boxK : ∀ a b, Pr (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3: provability is provably transitive. -/
  box4 : ∀ a, Pr (imp (box a) (box (box a)))
  /-- *Ex falso quodlibet*. -/
  efq : ∀ a, Pr (imp bot a)
  /-- The diagonal lemma: every `a` has a fixed point `l` provably equivalent to
  the sentence "if `l` is provable then `a`". -/
  diag : ∀ a, ∃ l, Pr (imp l (imp (box l) a)) ∧ Pr (imp (imp (box l) a) l)

namespace ProvabilityFrame

variable {S : Type u} (F : ProvabilityFrame S)

/-- The theory is *consistent* if it does not prove falsity. -/
def Consistent : Prop := ¬ F.Pr F.bot

/-- The *reflection sentence* for `a`: "if `a` is provable, then `a`". -/
def reflection (a : S) : S := F.imp (F.box a) a

variable {F}

/-- If the theory proves `a → b` then it proves `□a → □b`. -/
theorem box_mono {a b : S} (h : F.Pr (F.imp a b)) :
    F.Pr (F.imp (F.box a) (F.box b)) :=
  F.mp (F.boxK a b) (F.nec h)

/-- **Löb's theorem**: if the theory proves the reflection sentence for `a`,
then it proves `a`. -/
theorem loeb {a : S} (h : F.Pr (F.reflection a)) : F.Pr a := by
  obtain ⟨l, h1, h2⟩ := F.diag a
  -- `⊢ □l → □(□l → a)`
  have step2 : F.Pr (F.imp (F.box l) (F.box (F.imp (F.box l) a))) := box_mono h1
  -- `⊢ □(□l → a) → (□□l → □a)`
  have step3 : F.Pr (F.imp (F.box (F.imp (F.box l) a))
      (F.imp (F.box (F.box l)) (F.box a))) := F.boxK _ _
  -- `⊢ □l → (□□l → □a)`
  have step4 : F.Pr (F.imp (F.box l) (F.imp (F.box (F.box l)) (F.box a))) :=
    F.imp_trans step2 step3
  -- `⊢ □l → □a`
  have step6 : F.Pr (F.imp (F.box l) (F.box a)) := F.distrib step4 (F.box4 l)
  -- `⊢ □l → a`
  have step7 : F.Pr (F.imp (F.box l) a) := F.imp_trans step6 h
  -- hence `⊢ l`, so `⊢ □l`, so `⊢ a`
  exact F.mp step7 (F.nec (F.mp h2 step7))

/-- An inconsistent theory proves everything. -/
theorem pr_of_inconsistent (h : F.Pr F.bot) (a : S) : F.Pr a := F.mp (F.efq a) h

end ProvabilityFrame

/-- **No self trust (Löb).**  Let `F` be a theory with a provability predicate
satisfying the Hilbert–Bernays–Löb derivability conditions and the diagonal lemma,
and let `a` be a sentence that the theory does *not* prove.  Then:

* the theory is consistent, and
* it does not prove the reflection principle `□a → a` for `a`.

In words: a consistent theory can never prove "if `a` is provable then `a`" for a
sentence `a` it cannot already prove — it cannot trust itself.  (Taking `a = ⊥`
gives Gödel's second incompleteness theorem, see `Frontier.goedel_second`.) -/
theorem loeb_no_self_trust {S : Type u} (F : ProvabilityFrame S) {a : S}
    (ha : ¬ F.Pr a) : F.Consistent ∧ ¬ F.Pr (F.reflection a) :=
  ⟨fun hbot => ha (ProvabilityFrame.pr_of_inconsistent hbot a),
    fun h => ha (ProvabilityFrame.loeb h)⟩

/-- **Gödel's second incompleteness theorem** as a corollary: a consistent theory
does not prove its own consistency statement `□⊥ → ⊥`. -/
theorem goedel_second {S : Type u} (F : ProvabilityFrame S) (hcon : F.Consistent) :
    ¬ F.Pr (F.reflection F.bot) :=
  (loeb_no_self_trust F hcon).2

/-- The axioms of `ProvabilityFrame` are satisfiable together with the existence of an
unprovable sentence, so `loeb_no_self_trust` is not vacuous: take sentences to be
Lean propositions, `Pr` to be truth, and `box` the constant `True`. -/
theorem exists_frame_with_unprovable_sentence :
    ∃ (F : ProvabilityFrame Prop) (a : Prop), ¬ F.Pr a := by
  refine ⟨{ imp := fun p q => p → q, bot := False, box := fun _ => True, Pr := id,
            mp := fun h ha => h ha, nec := fun _ => trivial,
            imp_trans := fun h1 h2 x => h2 (h1 x),
            distrib := fun h1 h2 x => h1 x (h2 x),
            boxK := fun _ _ _ _ => trivial, box4 := fun _ _ => trivial,
            efq := fun _ h => h.elim,
            diag := fun a => ⟨a, fun ha _ => ha, fun h => h trivial⟩ }, False, id⟩

end Frontier


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

