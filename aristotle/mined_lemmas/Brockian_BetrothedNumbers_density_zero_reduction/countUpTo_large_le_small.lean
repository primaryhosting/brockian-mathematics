import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma countUpTo_large_le_small (N : ℕ) :
    countUpTo BetrothedLarge N ≤ countUpTo BetrothedSmall N := by
  refine Finset.card_le_card_of_injOn (fun n => sigmaOne n - n - 1) ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, m, hpair, hmn⟩ := hn
    have hm : sigmaOne n - n - 1 = m := (partner_eq hpair).symm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc, hm]
    refine ⟨⟨hpair.1, by omega⟩, n, isBetrothedPair_symm hpair, hmn⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb
    obtain ⟨_, ma, hpa, _⟩ := ha
    obtain ⟨_, mb, hpb, _⟩ := hb
    have hma : sigmaOne a - a - 1 = ma := (partner_eq hpa).symm
    have hmb : sigmaOne b - b - 1 = mb := (partner_eq hpb).symm
    have hab' : sigmaOne a - a - 1 = sigmaOne b - b - 1 := hab
    rw [hma, hmb] at hab'
    subst hab'
    obtain ⟨_, _, _, ha4, _⟩ := hpa
    obtain ⟨_, _, _, hb4, _⟩ := hpb
    omega

