/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

/-- Cohomological data attached to a variety over a finite field `𝔽_q`:
the inverse roots (Frobenius eigenvalues) on each cohomology group, together with the
point counts over the extensions `𝔽_{q^m}`, linked by the Grothendieck–Lefschetz trace
formula. -/
structure WeilVariety where
  /-- Cardinality of the base field. -/
  q : ℕ
  /-- The base field has at least two elements. -/
  hq : 2 ≤ q
  /-- Dimension of the variety. -/
  dim : ℕ
  /-- Multiset of inverse roots of Frobenius acting on the `i`-th cohomology group. -/
  frobRoots : ℕ → Multiset ℂ
  /-- `count m` is the number of `𝔽_{q^m}`-rational points. -/
  count : ℕ → ℕ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobRoots i = 0
  /-- Grothendieck–Lefschetz trace formula. -/
  trace : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1),
        (-1) ^ i * (((frobRoots i).map (fun a => a ^ m)).sum)

/-- The Riemann hypothesis for a variety over a finite field: every inverse root of
Frobenius on the `i`-th cohomology group has archimedean absolute value `q ^ (i / 2)`. -/

lemma multiset_pow_sum_norm_le (s : Multiset ℂ) (c : ℝ) (m : ℕ)
    (h : ∀ a ∈ s, ‖a‖ ≤ c) :
    ‖(s.map (fun a => a ^ m)).sum‖ ≤ (Multiset.card s : ℝ) * c ^ m := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : ‖a‖ ≤ c := h a (Multiset.mem_cons_self a s)
      have hc : (0:ℝ) ≤ c := le_trans (norm_nonneg a) ha
      have ih' : ‖(s.map (fun x => x ^ m)).sum‖ ≤ (Multiset.card s : ℝ) * c ^ m :=
        ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      have hpow : ‖a ^ m‖ ≤ c ^ m := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg a) ha m
      have : ‖(a ^ m) + (s.map (fun x => x ^ m)).sum‖ ≤ c ^ m + (Multiset.card s : ℝ) * c ^ m :=
        le_trans (norm_add_le _ _) (add_le_add hpow ih')
      simpa [Multiset.map_cons, Multiset.sum_cons, add_mul, add_comm, add_left_comm,
        add_assoc] using this

/-- Even-degree bookkeeping for the projective space example. -/
