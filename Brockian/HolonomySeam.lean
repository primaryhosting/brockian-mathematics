import Mathlib
import Brockian.HolonomyObservers

/-!
# Iterating the general seam map

The clock crosses the seam once in q steps. This connects the actual one-step
permutation to the loop translations used by the observer theorem.
-/

namespace Brockian.HolonomySeam

open Brockian.HolonomyObservers

variable (q m : ℕ) [NeZero q] [NeZero m]

theorem before_seam (h d : ZMod m) (n : ℕ) (hn : n < q) :
    (seamStep q m h)^[n] (0, d) = ((n : ZMod q), d) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hlast : (n : ZMod q) ≠ -1 := by
        intro heq
        have hz : ((n + 1 : ℕ) : ZMod q) = 0 := by
          push_cast
          rw [heq]
          ring
        have hd : q ∣ n + 1 := (ZMod.natCast_eq_zero_iff _ _).mp hz
        have hle := Nat.le_of_dvd (show 0 < n + 1 by omega) hd
        omega
      simp [seamStep, hlast, Nat.cast_add, Nat.cast_one]

theorem one_loop_at_zero (h d : ZMod m) :
    (seamStep q m h)^[q] (0, d) = (0, d + h) := by
  have hq : 0 < q := NeZero.pos q
  have hsum : q - 1 + 1 = q := by omega
  have hlast : ((q - 1 : ℕ) : ZMod q) = -1 := by
    have hz : ((q - 1 : ℕ) : ZMod q) + 1 = 0 := by
      rw [← Nat.cast_add_one, hsum, ZMod.natCast_self]
    linear_combination hz
  calc
    (seamStep q m h)^[q] (0, d) =
        (seamStep q m h)^[q - 1 + 1] (0, d) := by rw [hsum]
    _ = (0, d + h) := by
      rw [Function.iterate_succ_apply', before_seam q m h d (q - 1) (by omega)]
      simp [seamStep, hlast]

theorem one_loop (h : ZMod m) (x : ZMod q × ZMod m) :
    (seamStep q m h)^[q] x = (x.1, x.2 + h) := by
  have hx : (seamStep q m h)^[x.1.val] (0, x.2) = x := by
    simpa using before_seam q m h x.2 x.1.val (ZMod.val_lt x.1)
  calc
    (seamStep q m h)^[q] x =
        (seamStep q m h)^[q] ((seamStep q m h)^[x.1.val] (0, x.2)) := by rw [hx]
    _ = (seamStep q m h)^[x.1.val] ((seamStep q m h)^[q] (0, x.2)) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm q]
    _ = (seamStep q m h)^[x.1.val] (0, x.2 + h) := by rw [one_loop_at_zero]
    _ = (x.1, x.2 + h) := by
      simpa using before_seam q m h (x.2 + h) x.1.val (ZMod.val_lt x.1)

theorem completed_loops (h : ZMod m) (x : ZMod q × ZMod m) (r : ℕ) :
    (seamStep q m h)^[q * r] x = (x.1, x.2 + r • h) := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, one_loop, ih]
      simp [succ_nsmul, nsmul_eq_mul]
      <;> ring

theorem residue_after_steps (h : ZMod m) (x : ZMod q × ZMod m) (n : ℕ) :
    ((seamStep q m h)^[n] x).1 = x.1 + (n : ZMod q) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ((seamStep q m h)^[n] x).1 + 1 = x.1 + (↑(n + 1) : ZMod q)
      rw [ih]
      push_cast
      ring

theorem return_forces_whole_loops (h : ZMod m) (x : ZMod q × ZMod m) (n : ℕ)
    (hreturn : (seamStep q m h)^[n] x = x) : q ∣ n := by
  have hres := congrArg Prod.fst hreturn
  rw [residue_after_steps] at hres
  have hz : (n : ZMod q) = 0 := add_eq_left.mp hres
  exact (ZMod.natCast_eq_zero_iff n q).mp hz

theorem seam_return_iff (h n : ℕ) (x : ZMod q × ZMod m) :
    (seamStep q m (h : ZMod m))^[n] x = x ↔ q * (m / m.gcd h) ∣ n := by
  constructor
  · intro hret
    obtain ⟨r, rfl⟩ := return_forces_whole_loops q m (h : ZMod m) x n hret
    have hdepth := congrArg Prod.snd hret
    rw [completed_loops] at hdepth
    have hloops : (loop (h : ZMod m))^[r] x.2 = x.2 := by
      simpa only [loop_iterate] using hdepth
    obtain ⟨s, hs⟩ := (loop_return_iff h x.2 r).mp hloops
    exact ⟨s, by rw [hs]; ring⟩
  · rintro ⟨r, rfl⟩
    rw [Nat.mul_assoc, completed_loops]
    have hloops := (loop_return_iff h x.2 ((m / m.gcd h) * r)).mpr (dvd_mul_right _ _)
    rw [loop_iterate] at hloops
    exact Prod.ext rfl hloops

end Brockian.HolonomySeam
