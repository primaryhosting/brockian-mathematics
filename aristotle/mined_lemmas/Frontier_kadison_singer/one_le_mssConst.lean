/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-- Weaver's discrepancy-theoretic form `KS₂` of the Kadison–Singer problem, in dimension `d`,
with smallness parameter `ε` and discrepancy constant `C`.

Given finitely many vectors `v i` in `ℂ^d` which form a Parseval frame
(`∑ i, |⟪v i, x⟫|² = ‖x‖²` for all `x`, i.e. `∑ i, v i v i* = I`) and each of which is small
(`‖v i‖² ≤ ε`), the index set can be split into two halves each of which is a frame with
upper bound `C` (i.e. the operator norm of each of the two partial sums `∑ v i v i*` is at
most `C`).

The Marcus–Spielman–Srivastava theorem states that this holds for every `d` and every `ε > 0`
with `C = (1/√2 + √ε)²`. -/

theorem one_le_mssConst (ε : ℝ) (hε : 3 / 2 - Real.sqrt 2 ≤ ε) : 1 ≤ mssConst ε := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hε0 : 0 ≤ ε := by linarith
  set c : ℝ := 1 - Real.sqrt 2 / 2 with hc
  have hc0 : 0 ≤ c := by
    have : Real.sqrt 2 < 2 := by nlinarith
    rw [hc]; linarith
  have hcsq : c ^ 2 = 3 / 2 - Real.sqrt 2 := by
    rw [hc]; nlinarith
  have hcle : c ≤ Real.sqrt ε := (Real.le_sqrt hc0 hε0).mpr (by rw [hcsq]; linarith)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  have : (1:ℝ) = (1 / Real.sqrt 2 + c) ^ 2 := by
    rw [hinv, hc]; ring_nf
  rw [this]
  unfold mssConst
  have hnn : 0 ≤ 1 / Real.sqrt 2 + c := by positivity
  exact pow_le_pow_left₀ hnn (by linarith) 2

/-- **Kadison–Singer**, formalized in Weaver's `KS₂` discrepancy form with the
Marcus–Spielman–Srivastava constant `(1/√2 + √ε)²`.

Proved here:

* the base case `d = 1`, in full, for every smallness parameter `ε ≥ 0`;
* the regime `ε ≥ 3/2 - √2`, in every dimension `d`, where the MSS constant is already `≥ 1`. -/
