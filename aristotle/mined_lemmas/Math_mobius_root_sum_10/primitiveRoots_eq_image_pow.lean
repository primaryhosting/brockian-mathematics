import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- For a primitive `n`-th root of unity `ζ`, the finset of primitive `n`-th roots of unity is
the image of the residues coprime to `n` under `i ↦ ζ ^ i`. -/

lemma primitiveRoots_eq_image_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {ζ : R} {n : ℕ} [NeZero n] (h : IsPrimitiveRoot ζ n) :
    primitiveRoots n R = ((range n).filter (fun i => Nat.Coprime i n)).image (fun i => ζ ^ i) := by
  ext x
  rw [mem_primitiveRoots (NeZero.pos n), h.isPrimitiveRoot_iff]
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, hi, hc, rfl⟩; exact ⟨i, ⟨hi, hc⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hc⟩, rfl⟩; exact ⟨i, hi, hc, rfl⟩

/-- The Möbius function at `10` equals `1`. -/
