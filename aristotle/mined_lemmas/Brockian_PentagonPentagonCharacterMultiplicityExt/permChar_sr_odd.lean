import RequestProject.PentagonExt

/-!
# Decomposition of the vertex representation of a regular `n`-gon, `n` odd

For an odd number of vertices `n = 2m+1`, the permutation character of `DihedralGroup n`
acting on the vertices of the regular `n`-gon decomposes as the trivial character plus the
`m` two-dimensional characters `rotChar n 1, …, rotChar n m`.

For `n = 5` this is the classical pentagon statement `5 = 1 + 2 + 2`.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- For an odd `n`-gon every reflection fixes exactly one vertex. -/

lemma permChar_sr_odd [NeZero n] (hodd : Odd n) (i : ZMod n) : permChar n (sr i) = 1 := by
  have h2 : IsUnit (2 : ZMod n) := by
    have hc : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hodd
    simpa using (ZMod.isUnit_iff_coprime 2 n).mpr hc
  obtain ⟨u, hu⟩ := h2
  have key : fixedVertices n (sr i) = {(↑u⁻¹ * i : ZMod n)} := by
    ext x
    simp only [fixedVertices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      ngonAct_sr]
    constructor
    · intro h
      have hx : (u : ZMod n) * x = i := by rw [hu]; linear_combination -h
      rw [← hx, ← mul_assoc]
      simp
    · rintro rfl
      have hx : (u : ZMod n) * (↑u⁻¹ * i) = i := by rw [← mul_assoc]; simp
      rw [hu] at hx
      linear_combination -hx
  rw [permChar, key, Finset.card_singleton, Nat.cast_one]

/-- The value of the two-dimensional character on a rotation, expressed with roots of unity. -/
