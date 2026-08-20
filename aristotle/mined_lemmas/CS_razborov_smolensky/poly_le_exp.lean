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

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring, so the header above is
-- written as a plain block comment and repeated verbatim as a module docstring below.)

import RequestProject.RS.CircuitApprox
import RequestProject.RS.Smolensky
import RequestProject.RS.Binomial
import RequestProject.RS.Aux
import RequestProject.RS.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the Boolean function `MOD p`
(which tests whether the number of `1`s in the input is divisible by `p`) is not computed by any
family of constant-depth, polynomial-size circuits with unbounded fan-in AND, OR, NOT and
`MOD q` gates, i.e. `MOD p ∉ AC⁰[q]`.

The proof combines
* `CS.RS.Circuit.exists_approx`: every `AC⁰[q]` circuit is approximated, on all but a small
  fraction of the inputs, by a low-degree function over a field of characteristic `q`;
* `CS.RS.smolensky_bound`: a low-degree function can agree with `x ↦ ζ^(weight x)` (for `ζ` a
  primitive `p`-th root of unity) only on a set of inputs of size at most
  `∑_{i ≤ n/2 + D} C(n,i)`;
* `CS.RS.modq_mem_AC0q`: a non-vacuity check, exhibiting `MOD q` itself as a depth-one,
  linear-size circuit family of this kind;
* binomial estimates showing that this is less than the number of inputs left over by the
  approximation step.
-/

namespace CS

open Finset CS.RS

/-- Shifting the weight by `(p - r) % p` detects the residue `r` modulo `p`. -/

lemma poly_le_exp (A k : ℕ) : ∃ j₀ : ℕ, ∀ j ≥ j₀, A * (j+3)^k ≤ 2^j := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2:ℝ)) (by norm_num)
  have hpos : (0:ℝ) < 1 / (A * 4^k + 1) := by positivity
  have hev : ∀ᶠ j : ℕ in atTop, ((j:ℝ)^k / 2^j) < 1 / (A * 4^k + 1) :=
    hlim.eventually_lt_const hpos
  obtain ⟨j1, hj1⟩ := (Filter.eventually_atTop.1 hev)
  refine ⟨max j1 1, fun j hj => ?_⟩
  have hj1' : j ≥ j1 := le_trans (le_max_left _ _) hj
  have hjpos : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hreal := hj1 j hj1'
  have h2pos : (0:ℝ) < 2^j := by positivity
  have hb : (0:ℝ) < (A:ℝ)*4^k+1 := by positivity
  have hstep : ((A:ℝ) * 4^k + 1) * (j:ℝ)^k < 2^j := by
    rw [div_lt_iff₀ h2pos] at hreal
    calc ((A:ℝ) * 4^k + 1) * (j:ℝ)^k = (j:ℝ)^k * ((A:ℝ)*4^k+1) := by ring
      _ < (1 / ((A:ℝ) * 4^k + 1)) * 2^j * ((A:ℝ)*4^k+1) := (mul_lt_mul_iff_of_pos_right hb).2 hreal
      _ = 2^j := by field_simp
  have hfinal : ((A:ℝ) * ((j:ℝ)+3)^k) ≤ (A:ℝ) * 4^k * (j:ℝ)^k := by
    have h34 : ((j:ℝ)+3) ≤ 4 * j := by
      have h1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hjpos
      linarith
    have hp : ((j:ℝ)+3)^k ≤ (4*(j:ℝ))^k := pow_le_pow_left₀ (by positivity) h34 k
    calc (A:ℝ) * ((j:ℝ)+3)^k ≤ (A:ℝ) * (4*(j:ℝ))^k :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (A:ℝ) * 4^k * (j:ℝ)^k := by rw [mul_pow]; ring
  have hlt : ((A:ℝ) * ((j:ℝ)+3)^k) < 2^j := by
    calc (A:ℝ) * ((j:ℝ)+3)^k ≤ (A:ℝ)*4^k*(j:ℝ)^k := hfinal
      _ ≤ ((A:ℝ)*4^k+1) * (j:ℝ)^k := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < 2^j := hstep
  have hcast : ((A * (j+3)^k : ℕ) : ℝ) < ((2^j : ℕ) : ℝ) := by push_cast; exact hlt
  exact le_of_lt (by exact_mod_cast hcast)

/-- A power of a logarithm is eventually dominated by the identity. -/
