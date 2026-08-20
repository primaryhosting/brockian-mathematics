import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma sphere_sdiff_poles_paradoxical : Paradoxical O3 (S2 \ poles) := by
  refine paradoxical_of_free Phi (S2 \ poles) ?_ ?_
  · rintro w y ⟨x, ⟨hxS, hxp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show ‖Phi w • x‖ = 1
      rw [O3.norm_smul]; exact hxS
    · rintro ⟨-, u, hu, hufix⟩
      refine hxp ⟨hxS, w⁻¹ * u * w, ?_, ?_⟩
      · intro hc
        apply hu
        have h : u = w * w⁻¹ := by
          have h2 := congrArg (fun z => w * z * w⁻¹) hc
          simpa [mul_assoc] using h2
        simpa using h
      · rw [map_mul, map_mul, SemigroupAction.mul_smul, SemigroupAction.mul_smul, hufix,
          map_inv, inv_smul_smul]
  · rintro x ⟨hxS, hxp⟩ w hfix
    by_contra hw
    exact hxp ⟨hxS, w, hw, hfix⟩

/-- The countably many poles are absorbed by a suitable rotation about the `y`-axis:
the whole sphere is paradoxical. -/
