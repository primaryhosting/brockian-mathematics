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


theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [amo, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    ContinuousLinearMap.coe_coe]
  have h1 : (inner ℂ (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (1 : ℤ)) x) y : ℂ)
      = inner ℂ x (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (-1 : ℤ)) y) := by
    rw [inner_weightedComp]
    congr 1
    ext n
    simp
  have h2 : (inner ℂ (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (-1 : ℤ)) x) y : ℂ)
      = inner ℂ x (weightedComp (fun _ => 1) 1 (fun _ => by simp)
        (Equiv.addRight (1 : ℤ)) y) := by
    rw [inner_weightedComp]
    congr 1
    ext n
    simp
  have h3 : (inner ℂ (weightedComp (amoPotential lam alpha theta) (2 * |lam|)
        (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ) x) y : ℂ)
      = inner ℂ x (weightedComp (amoPotential lam alpha theta) (2 * |lam|)
        (norm_amoPotential_le lam alpha theta) (Equiv.refl ℤ) y) := by
    rw [inner_weightedComp]
    congr 1
    ext n
    simp only [weightedComp_apply, Equiv.refl_symm, Equiv.refl_apply, conj_amoPotential]
  rw [h1, h2, h3]
  ring

/-- The spectrum of the almost Mathieu operator, viewed as a subset of the real line. -/
