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

lemma card_sum_zero_le {K : Type*} [Field K] {m : ℕ} (u : Fin m → K) (t₀ : Fin m) (h0 : u t₀ ≠ 0) :
    2 * ((univ : Finset (Finset (Fin m))).filter (fun S => ∑ t ∈ S, u t = 0)).card
      ≤ Fintype.card (Finset (Fin m)) := by
  classical
  set B := (univ : Finset (Finset (Fin m))).filter (fun S => ∑ t ∈ S, u t = 0) with hB
  set phi : Finset (Fin m) → Finset (Fin m) :=
    fun S => if t₀ ∈ S then S.erase t₀ else insert t₀ S with hphi
  have hinv : ∀ S, phi (phi S) = S := by
    intro S
    by_cases h : t₀ ∈ S
    · simp [hphi, h, Finset.insert_erase h]
    · simp [hphi, h, Finset.erase_insert h]
  have hmaps : ∀ S ∈ B, phi S ∈ Bᶜ := by
    intro S hS
    have hsum : ∑ t ∈ S, u t = 0 := (mem_filter.1 hS).2
    simp only [Finset.mem_compl, hB, mem_filter, mem_univ, true_and]
    intro hc
    by_cases h : t₀ ∈ S
    · have hs : ∑ t ∈ S.erase t₀, u t + u t₀ = ∑ t ∈ S, u t := Finset.sum_erase_add _ _ h
      rw [hsum] at hs
      simp only [hphi, if_pos h] at hc
      rw [hc, zero_add] at hs
      exact h0 hs
    · have hs : ∑ t ∈ insert t₀ S, u t = u t₀ + ∑ t ∈ S, u t := Finset.sum_insert h
      rw [hsum, add_zero] at hs
      simp only [hphi, if_neg h] at hc
      rw [hc] at hs
      exact h0 hs.symm
  have hinj : Set.InjOn phi B := by
    intro a _ b _ hab
    have h := congrArg phi hab
    rwa [hinv, hinv] at h
  have hcard : B.card ≤ Bᶜ.card := Finset.card_le_card_of_injOn phi hmaps hinj
  have hc2 : Bᶜ.card = Fintype.card (Finset (Fin m)) - B.card := Finset.card_compl B
  have hble : B.card ≤ Fintype.card (Finset (Fin m)) := Finset.card_le_univ B
  omega

/-- At most a `2^(-ℓ)` fraction of the `ℓ`-tuples of subsets have all sums vanishing. -/
