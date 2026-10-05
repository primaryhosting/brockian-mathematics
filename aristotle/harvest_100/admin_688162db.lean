/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- An abstract formal theory equipped with a provability predicate satisfying the
Hilbert–Bernays–Löb derivability conditions, together with the diagonal (fixed point)
lemma.  This is exactly the amount of structure that arithmetized metamathematics
(e.g. Peano Arithmetic with its standard proof predicate) provides.

* `Sentence` : the type of sentences of the theory;
* `imp a b`  : the (object level) implication `a → b`;
* `bot`      : the (object level) falsum;
* `Thm a`    : the (meta level) assertion that the theory proves `a`;
* `Pr a`     : the sentence "`a` is provable in the theory" (the arithmetized
  provability statement, i.e. `Prov(⌈a⌉)`).
-/
structure Theory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Object level implication. -/
  imp : Sentence → Sentence → Sentence
  /-- Object level falsum. -/
  bot : Sentence
  /-- `Thm a` means: the theory proves the sentence `a`. -/
  Thm : Sentence → Prop
  /-- `Pr a` is the sentence expressing "`a` is provable in the theory". -/
  Pr : Sentence → Sentence
  /-- Propositional axiom scheme K. -/
  ax_k : ∀ a b : Sentence, Thm (imp a (imp b a))
  /-- Propositional axiom scheme S. -/
  ax_s : ∀ a b c : Sentence,
    Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Ex falso quodlibet. -/
  ax_bot : ∀ a : Sentence, Thm (imp bot a)
  /-- Closure of the theory under modus ponens. -/
  mp : ∀ {a b : Sentence}, Thm (imp a b) → Thm a → Thm b
  /-- First derivability condition: the theory proves its own proofs. -/
  D1 : ∀ {a : Sentence}, Thm a → Thm (Pr a)
  /-- Second derivability condition: internal closure of provability under modus ponens. -/
  D2 : ∀ a b : Sentence, Thm (imp (Pr (imp a b)) (imp (Pr a) (Pr b)))
  /-- Third derivability condition: provable sentences are provably provable. -/
  D3 : ∀ a : Sentence, Thm (imp (Pr a) (Pr (Pr a)))
  /-- Diagonal lemma: every sentence `a` has a fixed point `p` provably equivalent to
  `Pr p → a`. -/
  diag : ∀ a : Sentence, ∃ p : Sentence,
    Thm (imp p (imp (Pr p) a)) ∧ Thm (imp (imp (Pr p) a) p)

namespace Theory

variable (T : Theory)

/-- A theory is consistent when it does not prove falsum. -/
def Consistent : Prop := ¬ T.Thm T.bot

/-- The *reflection principle* (or local reflection sentence, "self trust") for a
sentence `a`: the sentence `Pr(⌈a⌉) → a`, asserting that provability of `a` implies `a`. -/
def Reflection (a : T.Sentence) : T.Sentence := T.imp (T.Pr a) a

variable {T}

/-- Reflexivity of object level implication. -/
theorem imp_self (a : T.Sentence) : T.Thm (T.imp a a) := by
  have h1 : T.Thm (T.imp (T.imp a (T.imp (T.imp a a) a)) (T.imp (T.imp a (T.imp a a)) (T.imp a a))) :=
    T.ax_s a (T.imp a a) a
  exact T.mp (T.mp h1 (T.ax_k a (T.imp a a))) (T.ax_k a a)

/-- A provable sentence is provably implied by anything. -/
theorem imp_intro_left {b : T.Sentence} (a : T.Sentence) (hb : T.Thm b) :
    T.Thm (T.imp a b) :=
  T.mp (T.ax_k b a) hb

/-- Distribution of a proved implication over a proved antecedent. -/
theorem imp_distrib {a b c : T.Sentence} (h1 : T.Thm (T.imp a (T.imp b c)))
    (h2 : T.Thm (T.imp a b)) : T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_s a b c) h1) h2

/-- Transitivity (syllogism) of object level implication. -/
theorem imp_trans {a b c : T.Sentence} (h1 : T.Thm (T.imp a b)) (h2 : T.Thm (T.imp b c)) :
    T.Thm (T.imp a c) :=
  imp_distrib (imp_intro_left a h2) h1

/-- **Löb's theorem.**  If a theory proves the reflection sentence `Pr(⌈a⌉) → a`,
then it already proves `a`. -/
theorem loeb {a : T.Sentence} (h : T.Thm (T.Reflection a)) : T.Thm a := by
  obtain ⟨p, hp1, hp2⟩ := T.diag a
  -- `Pr p → Pr (Pr p → a)`
  have s3 : T.Thm (T.imp (T.Pr p) (T.Pr (T.imp (T.Pr p) a))) :=
    T.mp (T.D2 p (T.imp (T.Pr p) a)) (T.D1 hp1)
  -- `Pr p → (Pr (Pr p) → Pr a)`
  have s5 : T.Thm (T.imp (T.Pr p) (T.imp (T.Pr (T.Pr p)) (T.Pr a))) :=
    imp_trans s3 (T.D2 (T.Pr p) a)
  -- `Pr p → Pr a`
  have s7 : T.Thm (T.imp (T.Pr p) (T.Pr a)) := imp_distrib s5 (T.D3 p)
  -- `Pr p → a`
  have s8 : T.Thm (T.imp (T.Pr p) a) := imp_trans s7 h
  have s9 : T.Thm p := T.mp hp2 s8
  exact T.mp s8 (T.D1 s9)

end Theory

/-- **A consistent theory cannot trust itself about an unprovable sentence.**

If `T` is a theory satisfying the Hilbert–Bernays–Löb derivability conditions and the
diagonal lemma, `T` is consistent, and `a` is a sentence that `T` does not prove, then
`T` does not prove its own reflection principle `Pr(⌈a⌉) → a` for `a`.

(The consistency hypothesis `hcon` is stated because it is part of the informal
statement; by Löb's theorem the conclusion in fact already follows from the
unprovability of `a` alone.) -/
theorem loeb_no_self_trust (T : Theory) (hcon : T.Consistent) (a : T.Sentence)
    (ha : ¬ T.Thm a) : ¬ T.Thm (T.Reflection a) := by
  intro h
  exact ha (Theory.loeb h)

/-- Consequence: a consistent theory cannot prove the *uniform* local reflection
schema, i.e. it cannot prove `Pr(⌈a⌉) → a` for every sentence `a`. -/
theorem no_uniform_self_trust (T : Theory) (hcon : T.Consistent) :
    ¬ ∀ a : T.Sentence, T.Thm (T.Reflection a) := by
  intro h
  exact hcon (Theory.loeb (h T.bot))

/-- Sanity check: the axioms of `Frontier.Theory` are satisfiable (by the degenerate
theory that proves everything).  Of course this example is *not* consistent, in
accordance with `Frontier.no_uniform_self_trust`. -/
example : Theory where
  Sentence := Unit
  imp _ _ := ()
  bot := ()
  Thm _ := True
  Pr _ := ()
  ax_k _ _ := trivial
  ax_s _ _ _ := trivial
  ax_bot _ := trivial
  mp _ _ := trivial
  D1 _ := trivial
  D2 _ _ := trivial
  D3 _ := trivial
  diag _ := ⟨(), trivial, trivial⟩

end Frontier

