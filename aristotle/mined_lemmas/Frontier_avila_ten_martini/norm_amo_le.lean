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

## Contents

* `Frontier.amo`: the almost Mathieu operator `H_{lam, alpha, theta}` on `ℓ²(ℤ)`, constructed as
  a bounded operator from a general bounded weighted composition operator.
* `Frontier.amo_isSelfAdjoint`: it is selfadjoint.
* `Frontier.amoSpectrum`: its spectrum, as a subset of `ℝ`; it is nonempty, compact and contained
  in `[-(2 + 2|lam|), 2 + 2|lam|]`.
* `Frontier.IsCantorSet`: nonempty, compact, perfect and totally disconnected subsets of `ℝ`.
* `Frontier.avila_ten_martini`: the Ten Martini statement, reduced (with a Lean-checked proof) to
  the two analytic inputs of the Avila–Jitomirskaya theorem, namely that the spectrum has no
  isolated points and that all spectral gaps are open.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ)` and weighted shift operators -/

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0:ℤ) (1:ℂ), 0, ?_⟩
  intro h
  have hval := congrArg (fun f : L2Z => (f : ℤ → ℂ) 0) h
  simp at hval


theorem norm_amo_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  have h1 := norm_weightedComp_le (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp)
    (Equiv.addRight (1 : ℤ))
  have h2 := norm_weightedComp_le (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp)
    (Equiv.addRight (-1 : ℤ))
  have h3 := norm_weightedComp_le (amoPotential lam alpha theta) (2 * |lam|)
    (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ)
  have hsum := norm_add_le
    (weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (1 : ℤ))
      + weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (-1 : ℤ)))
    (weightedComp (amoPotential lam alpha theta) (2 * |lam|)
      (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ))
  have hsum' := norm_add_le
    (weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (1 : ℤ)))
    (weightedComp (fun _ : ℤ => (1:ℂ)) 1 (fun _ => by simp) (Equiv.addRight (-1 : ℤ)))
  calc ‖amo lam alpha theta‖ ≤ _ := hsum
    _ ≤ 2 + 2 * |lam| := by linarith

/-- The inner product on `ℓ²(ℤ)` as a sum. -/
