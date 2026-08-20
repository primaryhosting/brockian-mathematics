import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

theorem integral_id_div_one_add_exp :
    (∫ t in Ioi (0 : ℝ), t / (1 + rexp t)) = π ^ 2 / 12 := by
  have hp : ∀ i : ℕ, etaCoeff i = 0 ∨ 0 < (i : ℝ) := by
    intro i
    by_cases h : i = 0
    · left; simp [etaCoeff, h]
    · right; exact_mod_cast Nat.pos_of_ne_zero h
  have hs : 0 < (2 : ℂ).re := by norm_num
  have key := hasSum_mellin hp hs (fun t ht => hasSum_fermiDirac ht) summable_etaCoeff
  have hGamma : Complex.Gamma 2 = 1 := by simp
  have hterm : ∀ n : ℕ, Complex.Gamma 2 * etaCoeff n / (n : ℂ) ^ (2 : ℂ)
      = (((-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [hGamma, one_mul]
    by_cases h : n = 0
    · subst h; simp [etaCoeff]
    · rw [Complex.cpow_two]
      simp only [etaCoeff, if_neg h]
      push_cast
      ring
  have key2 : HasSum (fun n : ℕ => (((-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 : ℝ) : ℂ)) (mellin fermiDirac 2) :=
    key.congr_fun (fun n => (hterm n).symm)
  have key3 : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2) (π ^ 2 / 12) := hasSum_eta_two
  have hmel : mellin fermiDirac 2 = ((π ^ 2 / 12 : ℝ) : ℂ) :=
    key2.unique (Complex.hasSum_ofReal.mpr key3)
  rw [mellin] at hmel
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      (t : ℂ) ^ ((2 : ℂ) - 1) • fermiDirac t = (((t / (1 + rexp t) : ℝ)) : ℂ) := by
    intro t _
    simp only [fermiDirac, smul_eq_mul]
    rw [show (2 : ℂ) - 1 = 1 by ring, Complex.cpow_one]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal] at hmel
  exact_mod_cast hmel

end Mirzakhani

/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.EtaIntegral
import RequestProject.Kernel

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We formalize Mirzakhani's recursion for the Weil–Petersson volumes
`V_{g,n}(L_1, …, L_n)` of moduli spaces of bordered hyperbolic surfaces of genus `g`
with `n` geodesic boundary components of lengths `L_1, …, L_n`.

Since `V_{g,n}` is a symmetric function of the boundary lengths, a volume function is
modelled here as a map `V : ℕ → Multiset ℝ → ℝ`, where `V g s` stands for
`V_{g, |s|}` evaluated at the boundary lengths listed by the multiset `s`.
The stability condition `2g - 2 + n > 0` is written `3 ≤ 2 * g + |s|`.

Mirzakhani's recursion is the identity

`∂/∂L₁ (L₁ · V_{g,n}(L₁, L̂)) = A^con + A^dcon + B`

with

* `A^con = ½ ∫∫ x y H(x+y, L₁) V_{g-1,n+1}(x, y, L̂) dx dy`,
* `A^dcon = ½ ∫∫ x y H(x+y, L₁) Σ_{stable} V_{g₁}(x, I) V_{g₂}(y, J) dx dy`,
* `B = ½ Σ_j ∫ x (H(x, L₁+L_j) + H(x, L₁-L_j)) V_{g,n-1}(x, L̂_j) dx`,

where `H(x,y) = 1/(1+e^{(x+y)/2}) + 1/(1+e^{(x-y)/2})` and the sum in `A^dcon` runs over
all stable splittings `g₁ + g₂ = g`, `I ⊎ J = L̂`.  We use the integrated
(equivalent) form of the identity, which avoids differentiability side conditions:
`L₁ V_{g,n}(L₁, L̂) = ∫_0^{L₁} (A^con + A^dcon + B)(t) dt`.

The main results are:

* `Frontier.WPVolumeRecursion`: the formalized recursion (a predicate on volume functions),
* `Frontier.mirzakhani_WP_volume`: the base cases `V_{0,3} = 1`, `V_{1,1}(L) = (L²+4π²)/24`
  are propagated by the recursion to the Lean-checked reduction
  `V_{0,4}(L₁,…,L₄) = 2π² + ½ Σ L_i²`, and the recursion together with the base cases
  determines all Weil–Petersson volumes uniquely,
* `Frontier.mirzakhani_recursion_consistent`: the hypotheses feeding the four-holed sphere
  reduction are satisfiable, so that reduction is not vacuous.

The analytic input is the moment integral `Mirzakhani.integral_id_mul_H`,
`∫_0^∞ x H(x,y) dx = y²/2 + 2π²/3`, proved from `∫_0^∞ t/(1+e^t) dt = π²/12`, which in turn is
obtained as the Mellin transform of the Dirichlet eta function at `s = 2` (see the files
`RequestProject/Kernel.lean` and `RequestProject/EtaIntegral.lean`).

Full existence of a solution of the recursion in all stable ranges is Mirzakhani's theorem and
is not formalized here; all statements about volume functions are therefore conditional on
`WPVolumeRecursion`.
-/

open Real MeasureTheory Set Multiset
open scoped Real
open scoped BigOperators
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- The `A^con` term of Mirzakhani's recursion: the contribution of the surfaces obtained by
removing a pair of pants that meets the distinguished boundary in one boundary circle and whose
two other boundary circles are glued to a *connected* surface of genus `g-1`. -/
