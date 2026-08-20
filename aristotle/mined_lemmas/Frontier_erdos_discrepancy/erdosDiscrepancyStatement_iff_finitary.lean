/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` all of whose values on positive integers
are `1` or `-1`. -/

theorem erdosDiscrepancyStatement_iff_finitary :
    ErdosDiscrepancyStatement ↔ FinitaryErdosDiscrepancyStatement := by
  constructor
  · -- infinite ⟹ finitary, by compactness
    intro H
    by_contra hc
    unfold FinitaryErdosDiscrepancyStatement at hc
    push_neg at hc
    obtain ⟨C, hC⟩ := hc
    choose F hF1 hF2 using hC
    classical
    set U : Filter ℕ := (hyperfilter ℕ : Filter ℕ) with hU
    -- the ultrafilter limit of the counterexamples
    set g : ℕ → ℤ := fun i => if (∀ᶠ N in U, F N i = 1) then 1 else -1 with hg
    have hgpm : IsPlusMinusOne g := by
      intro n _
      by_cases h : (∀ᶠ N in U, F N n = 1) <;> simp [hg, h]
    have key : ∀ i, 1 ≤ i → ∀ᶠ N in U, F N i = g i := by
      intro i hi
      by_cases hcase : (∀ᶠ N in U, F N i = 1)
      · simp [hg, hcase]
      · have h1 : ∀ᶠ N in U, F N i ≠ 1 := Ultrafilter.eventually_not.mpr hcase
        have h2 : ∀ᶠ N in U, F N i = -1 := h1.mono fun N hN => ((hF1 N) i hi).resolve_left hN
        simpa [hg, hcase] using h2
    have hle : U ≤ atTop := by rw [hU, ← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite
    have bound : ∀ d n : ℕ, 0 < d → 0 < n → |apSum g d n| ≤ (C : ℤ) := by
      intro d n hd hn
      have hall : ∀ᶠ N in U, ∀ i ∈ Finset.Icc 1 n, F N (i * d) = g (i * d) :=
        (eventually_all_finset _).mpr (by
          intro i hi
          rw [Finset.mem_Icc] at hi
          exact key (i * d) (Nat.mul_pos hi.1 hd))
      have hbig : ∀ᶠ N in U, d * n ≤ N := hle (eventually_ge_atTop (d * n))
      have hev : ∀ᶠ N in U, |apSum g d n| ≤ (C : ℤ) := by
        filter_upwards [hall, hbig] with N h1 h2
        have he : apSum g d n = apSum (F N) d n :=
          Finset.sum_congr rfl fun i hi => (h1 i hi).symm
        rw [he]
        exact hF2 N d n hd hn h2
      obtain ⟨_, h⟩ := hev.exists
      exact h
    obtain ⟨d, n, hd, hn, hlt⟩ := H g hgpm C
    exact absurd (bound d n hd hn) (not_le.mpr hlt)
  · -- finitary ⟹ infinite
    intro H f hf C
    obtain ⟨N, hN⟩ := H C
    obtain ⟨d, n, hd, hn, -, hlt⟩ := hN f hf
    exact ⟨d, n, hd, hn, hlt⟩

end Frontier

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

