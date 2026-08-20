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

def sysSetoid (h : S → R → Z) (z₀ : Z) : Setoid S where
  r s s' := ∀ r, h s r = z₀ ↔ h s' r = z₀
  iseqv :=
    { refl := fun _ _ => Iff.rfl
      symm := fun hss' r => (hss' r).symm
      trans := fun h₁ h₂ r => (h₁ r).trans (h₂ r) }

section Model

variable (h : S → R → Z) (z₀ : Z) (hgood : ∀ s, ∃! r, h s r = z₀)

/-- The model of the system extracted from a perfectly regulable setup: `regulatorModel`
sends a system state to the unique regulator action that achieves the good outcome. -/
