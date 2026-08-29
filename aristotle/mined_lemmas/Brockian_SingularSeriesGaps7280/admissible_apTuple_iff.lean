import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
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

namespace Brockian

/-- The residues modulo `p` covered by the tuple `H`. -/

theorem admissible_apTuple_iff (k d : ℕ) :
    Admissible (apTuple k d) ↔ ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d := by
  constructor
  · intro hadm p hp hpk
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := hadm p hp
    by_contra hdvd
    have hd : (d : ZMod p) ≠ 0 := fun hc => hdvd ((ZMod.natCast_eq_zero_iff d p).mp hc)
    set i : ℕ := (r * (d : ZMod p)⁻¹).val with hi
    have hilt : i < p := ZMod.val_lt _
    have hmem : i * d ∈ apTuple k d :=
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le hilt hpk), rfl⟩
    refine hr (i * d) hmem ?_
    push_cast
    rw [hi, ZMod.natCast_val, ZMod.cast_id]
    field_simp
  · intro hdvd p hp
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_cases hpk : p ≤ k
    · -- all elements are `≡ 0 mod p`; the class of `1` is missed
      have hd : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr (hdvd p hp hpk)
      refine ⟨1, fun h hh => ?_⟩
      simp only [apTuple, Finset.mem_image, Finset.mem_range] at hh
      obtain ⟨i, _, rfl⟩ := hh
      push_cast
      rw [hd, mul_zero]
      exact fun hcon => one_ne_zero hcon.symm
    · -- fewer than `p` residues are covered
      push_neg at hpk
      refine card_coveredResidues_lt_iff.mp ?_
      calc (coveredResidues (apTuple k d) p).card
          ≤ (Finset.range k).card := by
            rw [coveredResidues_apTuple]; exact Finset.card_image_le
        _ = k := Finset.card_range k
        _ < p := hpk

/-- **Singular Series Gaps 7280.**

1.  A complete criterion for the admissibility of arithmetic-progression tuples
    `{0, d, 2d, …, (k-1)d}`: admissible exactly when every prime `p ≤ k` divides `d`.
2.  Equivalently, admissibility is the non-vanishing of all local singular-series factors.
3.  For the gap `d = 7280 = 2^4 · 5 · 7 · 13` the admissible lengths are exactly `k ≤ 2`.
4.  For the gap `d = 21840 = 3 · 7280 = 2^4 · 3 · 5 · 7 · 13` the admissible lengths extend
    all the way to `k ≤ 10`.
-/
