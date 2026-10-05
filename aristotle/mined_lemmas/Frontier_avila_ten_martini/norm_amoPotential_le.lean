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


theorem norm_amoPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    ‖amoPotential lam alpha theta n‖ ≤ 2 * |lam| := by
  have hcos : |Real.cos (2 * π * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  have hnorm : ‖amoPotential lam alpha theta n‖
      = |2 * lam * Real.cos (2 * π * (theta + n * alpha))| := by
    rw [amoPotential, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, abs_mul, abs_mul]
  have h2 : |(2:ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * π * (theta + n * alpha)))]

