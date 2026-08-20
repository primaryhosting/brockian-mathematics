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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ; ℂ)` on which the almost Mathieu operator acts. -/
abbrev Ell2 := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial Ell2 := by
  refine ⟨lp.single 2 0 1, 0, ?_⟩
  intro h
  have := congrArg (fun f : Ell2 => (f : ℤ → ℂ) 0) h
  simp at this


theorem isCantorSet_of_no_interior_no_isolated {S : Set ℝ} (hcomp : IsCompact S)
    (hne : S.Nonempty) (hint : interior S = ∅)
    (hacc : ∀ x ∈ S, AccPt x (Filter.principal S)) : IsCantorSet S :=
  ⟨hcomp, hne, ⟨hcomp.isClosed, hacc⟩, isTotallyDisconnected_of_interior_eq_empty hint⟩

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya): for every nonzero coupling constant `lam`,
every irrational flux `alpha` and every phase `theta`, the spectrum of the almost Mathieu
operator `H_{lam, alpha, theta}` is a Cantor set.

This is a *Lean-checked reduction* of the full theorem: the two deep analytic inputs are taken as
hypotheses, namely

* `h_noInterior`: the spectrum has empty interior (there are no bands: all spectral gaps
  predicted by the gap-labelling theorem are open);
* `h_noIsolated`: the spectrum has no isolated points.

Everything else is proved here from scratch: the almost Mathieu operator is constructed as a
bounded operator on `ℓ²(ℤ)`, it is shown to be self-adjoint with `‖H‖ ≤ 2 + 2|λ|`, its real
spectrum is shown to be nonempty and compact, and Cantor-ness (compact, nonempty, perfect,
totally disconnected) is deduced from the two hypotheses above.

The two analytic inputs are quantified over all admissible parameters, exactly as they appear in
the literature. -/
