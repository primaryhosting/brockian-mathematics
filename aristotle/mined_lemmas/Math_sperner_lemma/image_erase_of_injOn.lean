import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` lines to come first in a module, so the
required header block is placed immediately after the single `import Mathlib` line.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Codimension-one subsets -/

/-- Subsets of `S` of cardinality `S.card - 1` are exactly the sets `S.erase x` for `x ∈ S`;
hence counting them amounts to counting the vertices `x ∈ S` with the corresponding property. -/

lemma image_erase_of_injOn {color : V → ℕ} {S : Finset V} (hinj : Set.InjOn color S)
    {x : V} (hx : x ∈ S) :
    (S.erase x).image color = (S.image color).erase (color x) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨z, ⟨hzx, hzS⟩, rfl⟩
    exact ⟨fun h => hzx (hinj hzS hx h), z, hzS, rfl⟩
  · rintro ⟨hne, z, hzS, rfl⟩
    exact ⟨z, ⟨fun h => hne (by rw [h]), hzS⟩, rfl⟩

