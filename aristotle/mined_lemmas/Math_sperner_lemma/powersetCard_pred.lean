/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
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

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/

lemma powersetCard_pred (s : Finset V) (hs : s.Nonempty) :
    s.powersetCard (s.card - 1) = s.image (fun v => s.erase v) := by
  ext f
  simp only [Finset.mem_powersetCard, Finset.mem_image]
  constructor
  · rintro ⟨hfs, hcard⟩
    have hsd : (s \ f).card = 1 := by
      rw [Finset.card_sdiff_of_subset hfs, hcard]
      have : 1 ≤ s.card := Finset.card_pos.mpr hs
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hsd
    have hvmem : v ∈ s \ f := by rw [hv]; simp
    have hvs : v ∈ s := (Finset.mem_sdiff.mp hvmem).1
    have hvf : v ∉ f := (Finset.mem_sdiff.mp hvmem).2
    refine ⟨v, hvs, ?_⟩
    apply Finset.Subset.antisymm
    · intro u hu
      rcases Finset.mem_erase.mp hu with ⟨hne, hus⟩
      by_contra huf
      have : u ∈ s \ f := Finset.mem_sdiff.mpr ⟨hus, huf⟩
      rw [hv] at this
      exact hne (Finset.mem_singleton.mp this)
    · intro u hu
      exact Finset.mem_erase.mpr ⟨fun h => hvf (h ▸ hu), hfs hu⟩
  · rintro ⟨v, hvs, rfl⟩
    exact ⟨Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hvs]⟩

/-- If the fibre sizes of a partition of a set of size `B.card + 1` into `B.card` nonempty
parts are given by `m`, then exactly one part has two elements and all others one. -/
