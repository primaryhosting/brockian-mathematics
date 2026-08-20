/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/--
**Conant–Ashby "Good Regulator" theorem (deterministic base case).**

Setting: a system with state space `S`, a regulator with action space `R`, and an
outcome map `h : S → R → Z`.  The regulation goal is the single "good" outcome `z₀`
(the error-free, minimal-entropy case of the Conant–Ashby setup).

Hypothesis `hgood`: for every system state there is exactly one regulator action that
achieves the good outcome — i.e. regulation is possible and of minimal variety.

Conclusion: there is a map `m : S → R` such that

* `m` is a successful regulator;
* **every** good regulator equals `m`, so a good regulator is necessarily a *function of
  the system state*: it is a model of the system;
* `m s = m s'` holds exactly when `s` and `s'` impose the same requirement on the
  regulator.  Hence the regulator's actions are in bijection with the distinguishable
  states of the system: the regulator *contains a model* of the system.

The proof is elementary; the whole content is the uniqueness clause packaged in
`hgood` (this is exactly Mathlib's `ExistsUnique.unique`, spelled out here), so the file
needs no imports at all.
-/

theorem good_regulator {S R Z : Type _} (h : S → R → Z) (z₀ : Z)
    (hgood : ∀ s, ∃ r, h s r = z₀ ∧ ∀ r', h s r' = z₀ → r' = r) :
    ∃ m : S → R,
      (∀ s, h s (m s) = z₀) ∧
      (∀ ρ : S → R, (∀ s, h s (ρ s) = z₀) → ρ = m) ∧
      (∀ s s', m s = m s' ↔ ∀ r, (h s r = z₀ ↔ h s' r = z₀)) := by
  classical
  refine ⟨fun s => Classical.choose (hgood s), fun s => (Classical.choose_spec (hgood s)).1,
    ?_, ?_⟩
  · intro ρ hρ
    funext s
    exact (Classical.choose_spec (hgood s)).2 (ρ s) (hρ s)
  · intro s s'
    have hs := Classical.choose_spec (hgood s)
    have hs' := Classical.choose_spec (hgood s')
    show Classical.choose (hgood s) = Classical.choose (hgood s') ↔ _
    constructor
    · intro hss' r
      constructor
      · intro hr
        have hrs : r = Classical.choose (hgood s) := hs.2 r hr
        rw [hrs, hss']
        exact hs'.1
      · intro hr
        have hrs : r = Classical.choose (hgood s') := hs'.2 r hr
        rw [hrs, ← hss']
        exact hs.1
    · intro hiff
      exact hs'.2 _ ((hiff _).mp hs.1)

end Frontier

/-
# Good Regulator — Mathlib development

Companion file to `RequestProject/GoodRegulator.lean`, which contains the target
theorem `Frontier.good_regulator`.  (That file must open with a fixed header comment,
so it cannot carry an `import` line; the Mathlib-based development lives here.)

Here the Conant–Ashby statement is developed with Mathlib's `ExistsUnique`, and the
"contains a model" clause is upgraded to an explicit equivalence between the
distinguishable states of the system and the actions actually used by the regulator.
-/

import Mathlib

namespace Frontier

variable {S R Z : Type*}

/-- Two system states are *indistinguishable* (for the regulation goal `z₀`) when they
demand the same thing of the regulator: exactly the same actions succeed on both. -/
