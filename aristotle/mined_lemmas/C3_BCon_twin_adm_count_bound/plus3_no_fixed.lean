import Mathlib
namespace C3.BCon


theorem plus3_no_fixed (n : ℕ) (hn : 3 < n) (a : ZMod n) : a + 3 ≠ a := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  have h3 : (3 : ZMod n) = 0 := by
    have h' : a + 3 = a + 0 := by simpa using h
    exact add_left_cancel h'
  rw [show (3 : ZMod n) = ((3 : ℕ) : ZMod n) by push_cast; ring,
    ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

/-- There are exactly `4` nonzero residues modulo `5`. -/
