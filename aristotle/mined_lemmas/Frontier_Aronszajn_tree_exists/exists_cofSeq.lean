/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem exists_cofSeq {l : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) :
    ∃ c, IsCofSeq l c := by
  have hpos : (0 : Ordinal) < l := hl.bot_lt
  have hcount : (Set.Iio l).Countable := by
    rw [Cardinal.countable_iff_lt_aleph_one]
    have := Cardinal.lt_omega_iff_card_lt.mp hcl
    simpa [Ordinal.card, Ordinal.mk_Iio_ordinal] using this
  have hne : (Set.Iio l).Nonempty := ⟨0, hpos⟩
  obtain ⟨g, hg⟩ := hcount.exists_surjective hne
  refine ⟨fun n => (Finset.range n).sup (fun k => (g k : Ordinal) + 1), ?_, ?_, ?_, ?_⟩
  · simp
  · intro m n hmn
    exact Finset.sup_mono (by simpa using hmn)
  · intro n
    rw [Finset.sup_lt_iff (by rw [Ordinal.bot_eq_zero]; exact hpos)]
    intro k _
    exact hl.add_one_lt (g k).2
  · intro ξ hξ
    obtain ⟨k, hk⟩ := hg ⟨ξ, hξ⟩
    refine ⟨k + 1, ?_⟩
    have : ((g k : Ordinal) + 1) ≤ (Finset.range (k+1)).sup (fun j => (g j : Ordinal) + 1) :=
      Finset.le_sup (f := fun j => (g j : Ordinal) + 1) (Finset.self_mem_range_succ k)
    have hgk : (g k : Ordinal) = ξ := congrArg Subtype.val hk
    rw [hgk] at this
    exact lt_of_lt_of_le (lt_add_one ξ) this

open Classical in
/-- A canonical choice of cofinal `ω`-sequence. -/
