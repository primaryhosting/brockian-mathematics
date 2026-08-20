/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/


theorem IsCantorSet.not_countable {S : Set ℝ} (hS : IsCantorSet S) : ¬ S.Countable := by
  intro hc
  obtain ⟨f, hrange, -, hinj⟩ := hS.exists_nat_bool_injection
  have h1 : (Set.range f).Countable := hc.mono hrange
  have := h1.to_subtype
  exact not_countable_natToBool
    (Function.Injective.countable
      (f := fun x => (⟨f x, Set.mem_range_self x⟩ : Set.range f))
      (fun a b hab => hinj (congrArg Subtype.val hab)))

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya), formalized as a Lean-checked reduction.

For every nonzero coupling constant `lam`, every irrational flux `alpha` and every phase
`theta`, the spectrum of the almost Mathieu operator
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`
on `ℓ²(ℤ, ℂ)` is a Cantor set.

The two analytic inputs of the theorem are taken as hypotheses:
* `h_nowhere_dense`: the spectrum has empty interior (this is the hard "dry/dense gaps"
  content of the Ten Martini Problem, i.e. all gaps predicted by the gap-labelling theorem
  are open);
* `h_no_isolated`: the spectrum has no isolated points.

Everything else is proved here from the definition of the operator: the spectrum is
nonempty (via self-adjointness and nonemptiness of the complex spectrum), compact, and
empty interior in `ℝ` forces total disconnectedness.

The hypotheses `hlam : lam ≠ 0` and `halpha : Irrational alpha` are part of the classical
statement; they are what makes the two analytic inputs above true, and are not otherwise
used in this reduction. -/
