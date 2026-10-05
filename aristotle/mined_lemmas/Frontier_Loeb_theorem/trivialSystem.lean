/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

Mathlib does not contain Gödel's incompleteness theorems, a provability predicate for
Peano Arithmetic, or provability logic (a search for `Provable`, `Loeb`, `Godel`,
`Diagonal` turns up nothing usable), so the statement is formalized from scratch in the
standard abstract way.

Löb's theorem is a statement about *any* theory `T` (such as `PA`) equipped with a
provability predicate `□` satisfying the Hilbert–Bernays–Löb derivability conditions and
for which the diagonal (fixed point) lemma holds.  We package exactly these data as
`Frontier.ProvabilitySystem`:

* `Form`, `imp`, `box`, `Provable` : formulas, implication, the provability predicate
  `□` (for PA: `Prov_PA(⌜·⌝)`), and the derivability relation `PA ⊢ ·`;
* `ax_K`, `ax_S`, `mp` : the theory is closed under modus ponens and proves the
  standard implicational tautologies (any theory containing propositional logic does);
* `D1` (necessitation: `⊢ φ` implies `⊢ □φ`),
  `D2` (`⊢ □(φ → ψ) → (□φ → □ψ)`),
  `D3` (`⊢ □φ → □□φ`) : the three derivability conditions, all provable for PA;
* `diagonal` : the Gödel–Carnap diagonal lemma, which for every `φ` produces a sentence
  `γ` with `PA ⊢ γ ↔ (□γ → φ)`.

`Frontier.Loeb_theorem` then states: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`.

`Frontier.trivialSystem` witnesses that the hypotheses are satisfiable, so the theorem is
not vacuous.
-/

universe u

namespace Frontier

/-- An abstract theory (think: Peano Arithmetic) together with a provability predicate
`box` satisfying the Hilbert–Bernays–Löb derivability conditions and the diagonal lemma. -/
structure ProvabilitySystem where
  /-- The type of formulas (sentences) of the theory. -/
  Form : Type u
  /-- Implication of formulas, `imp p q` is `p → q`. -/
  imp : Form → Form → Form
  /-- The provability predicate `□`; for `PA` this is `φ ↦ Prov_PA(⌜φ⌝)`. -/
  box : Form → Form
  /-- `Provable p` means the theory proves `p`, i.e. `PA ⊢ p`. -/
  Provable : Form → Prop
  /-- The tautology `p → (q → p)`. -/
  ax_K : ∀ p q, Provable (imp p (imp q p))
  /-- The tautology `(p → (q → r)) → ((p → q) → (p → r))`. -/
  ax_S : ∀ p q r, Provable (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Modus ponens: the theory is closed under detachment. -/
  mp : ∀ {p q}, Provable (imp p q) → Provable p → Provable q
  /-- First derivability condition (necessitation): if `⊢ p` then `⊢ □p`. -/
  D1 : ∀ {p}, Provable p → Provable (box p)
  /-- Second derivability condition: `⊢ □(p → q) → (□p → □q)`. -/
  D2 : ∀ p q, Provable (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: `⊢ □p → □□p`. -/
  D3 : ∀ p, Provable (imp (box p) (box (box p)))
  /-- Diagonal (fixed point) lemma: every `p` has a fixed point `γ` with
  `⊢ γ ↔ (□γ → p)`, presented as the two implications. -/
  diagonal : ∀ p, ∃ g, Provable (imp g (imp (box g) p)) ∧
      Provable (imp (imp (box g) p) g)

namespace ProvabilitySystem

variable (S : ProvabilitySystem.{u})

/-- Hypothetical syllogism: from `⊢ a → b` and `⊢ b → c` infer `⊢ a → c`. -/

def trivialSystem : ProvabilitySystem.{u} where
  Form := PUnit
  imp _ _ := PUnit.unit
  box _ := PUnit.unit
  Provable _ := True
  ax_K _ _ := trivial
  ax_S _ _ _ := trivial
  mp _ _ := trivial
  D1 _ := trivial
  D2 _ _ := trivial
  D3 _ := trivial
  diagonal _ := ⟨PUnit.unit, trivial, trivial⟩

end Frontier

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

