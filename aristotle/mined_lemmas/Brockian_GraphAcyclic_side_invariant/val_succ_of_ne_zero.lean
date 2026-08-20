import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

lemma val_succ_of_ne_zero {x y : ZMod M} (h : y = x + 1) (hy : y ≠ 0) :
    ((y.val : ℤ)) = (x.val : ℤ) + 1 := by
  have hM : 1 < M := by
    by_contra hle
    push_neg at hle
    interval_cases M
    · exact NeZero.ne (n := 0) rfl
    · rw [h] at hy
      exact hy (by subsingleton)
  haveI : Fact (1 < M) := ⟨hM⟩
  rw [h]
  have h1 : (x + 1).val = (x.val + 1) % M := by
    rw [ZMod.val_add]
    have : ZMod.val 1 = 1 := ZMod.val_one (n := M)
    simp [this]
  have hxv : x.val < M := ZMod.val_lt x
  have hne : (x + 1).val ≠ 0 := by
    rw [h] at hy
    simp [ZMod.val_eq_zero]
    exact hy
  rw [h1] at hne
  have hlt : x.val + 1 < M := by
    by_contra hge
    push_neg at hge
    have : x.val + 1 = M := Nat.le_antisymm (Nat.succ_le_of_lt hxv) hge
    simp [this] at hne
  rw [h1, Nat.mod_eq_of_lt hlt]
  norm_cast

/-- The height of a twin-admissible residue: the position of `a` along the `+3` cycle. -/
