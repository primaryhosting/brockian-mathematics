import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


theorem cmach_complete (hnr : ¬ Relation.ReflTransGen (Rl r x) s t) :
    (cmach r s t).Accepts x := by
  have hcm : cnt (RS r s x m) ≤ m := cnt_le _
  obtain ⟨im, him⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
  obtain ⟨cm, hcmv⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cnt (RS r s x m) :=
    ⟨⟨cnt (RS r s x m), by omega⟩, rfl⟩
  obtain ⟨jm, hjm⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
  have hlevels := level_loop r s t x m le_rfl im cm him hcmv
  have hstart := hlevels.tail
    (stepT5' r s t x im cm 0 0 0 0 (val_zero' m) (val_zero' m) (val_zero' m) (val_zero' m))
  have hnotin : ¬ RS r s x ((im : ℕ) + 1) t := by
    rw [him]
    intro hmem
    exact hnr ((reach_iff_RS r s x t).mpr hmem)
  have hloop := no_loop r s t x im cm 0 0 t hnotin m le_rfl jm cm hjm
    (by rw [hcmv, him, cntb_full])
  exact (hstart.trans hloop).tail (stepT12 r s t x im cm 0 0 jm cm him hjm rfl)

end CS

import Mathlib

/-!
# A model of nondeterministic logarithmic space

We model a nondeterministic space bounded machine by its *configuration graph*.

For an input length `n`, a machine is a finite set `V` of configurations, an initial
configuration, an accepting configuration, and, for each ordered pair of configurations,
a *guard*: an atomic condition on the input, which is either "never", "always", or
"the `i`-th input bit equals `b`".  This is exactly the way a space bounded machine
depends on its input: a transition out of a configuration is determined by the finite
control together with the single input bit currently scanned.

The machine accepts an input `x` when the accepting configuration is reachable from the
initial one in the graph of the guards that hold under `x`.

The class `NL` is the class of languages recognised by such machines whose configuration
graph has polynomially many vertices, i.e. `O(log n)` space.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

/-- An atomic guard on an input of length `n`: an edge of a configuration graph is
either absent, present unconditionally, or present exactly when the `i`-th input bit
equals `b`. -/
inductive Lit (n : ℕ) where
  | never : Lit n
  | always : Lit n
  | test : Fin n → Bool → Lit n
  deriving DecidableEq

/-- Whether a guard holds on the input `x`. -/
