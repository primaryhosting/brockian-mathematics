import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_four_pow_mul_reduced (n : ℕ) (hn0 : n ≠ 0) (h : ¬ is_three_square_exception n) :
    ∃ a t : ℕ, n = 4 ^ a * t ∧ (¬ 4 ∣ t) ∧ t % 8 ≠ 7 := by
  classical
  -- Write `n = 2^k * m` with `2 ∤ m`.
  obtain ⟨k, m, hm2, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by decide : (2 : ℕ) ≠ 1)
  -- Split off powers of `4 = 2^2` from `2^k`.
  let a : ℕ := k / 2
  let b : ℕ := k % 2
  have hk : k = 2 * a + b := by
    -- `k = 2*(k/2) + k%2`
    simpa [a, b] using (Nat.div_add_mod k 2).symm
  have hb_lt : b < 2 := Nat.mod_lt k (by decide : 0 < 2)
  have hb : b = 0 ∨ b = 1 := by
    omega
  have hpow : 2 ^ k = 4 ^ a * 2 ^ b := by
    -- `2^k = 2^(2*a+b) = 2^(2*a) * 2^b = (2^2)^a * 2^b = 4^a * 2^b`
    calc
      2 ^ k = 2 ^ (2 * a + b) := by simp [hk]
      _ = 2 ^ (2 * a) * 2 ^ b := by simp [pow_add]
      _ = (2 ^ 2) ^ a * 2 ^ b := by simp [pow_mul]
      _ = 4 ^ a * 2 ^ b := by simp [pow_two]
  -- Define the reduced factor `t := 2^b * m`.
  let t : ℕ := 2 ^ b * m
  have hn' : n = 4 ^ a * t := by
    -- `n = 2^k * m = (4^a * 2^b) * m = 4^a * (2^b * m)`
    calc
      n = 2 ^ k * m := hnm
      _ = (4 ^ a * 2 ^ b) * m := by simp [hpow, Nat.mul_assoc]
      _ = 4 ^ a * (2 ^ b * m) := by ring_nf
      _ = 4 ^ a * t := by rfl
  have ht4 : ¬ 4 ∣ t := by
    -- Since `t = 2^b * m` with `b ∈ {0,1}` and `2 ∤ m`, we have `4 ∤ t`.
    rcases hb with hb0 | hb1
    · -- `b = 0` so `t = m`, and `4 ∣ m → 2 ∣ m`, contradicting `hm2`.
      have ht : t = m := by simp [t, hb0]
      intro h4t
      have h4m : 4 ∣ m := by simpa [ht] using h4t
      have h2m : 2 ∣ m := dvd_trans (by exact ⟨2, rfl⟩) h4m
      exact hm2 h2m
    · -- `b = 1` so `t = 2*m`. If `4 ∣ 2*m` then `2 ∣ m`, contradicting `hm2`.
      have ht : t = 2 * m := by simp [t, hb1]
      intro h4t
      have h4tm : 4 ∣ 2 * m := by simpa [ht] using h4t
      rcases h4tm with ⟨k, hk⟩
      have hk' : 2 * m = 2 * (2 * k) := by
        have h4 : 4 * k = 2 * (2 * k) := by ring
        exact hk.trans h4
      have hm_eq : m = 2 * k := Nat.mul_left_cancel (show 0 < 2 from by decide) hk'
      have h2m : 2 ∣ m := ⟨k, hm_eq⟩
      exact hm2 h2m

  refine ⟨a, t, hn', ht4, ?_⟩
  intro ht7
  -- If `t % 8 = 7`, then `t = 8*(t/8)+7`, hence `n` is an exception: contradiction.
  have ht_eq : t = 8 * (t / 8) + 7 := by
    have := (Nat.div_add_mod t 8).symm
    -- `t = 8*(t/8) + t%8`, then rewrite `t%8` to `7`.
    simpa [ht7, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using this
  apply h
  refine ⟨a, t / 8, ?_⟩
  -- `n = 4^a * (8*(t/8)+7)`
  calc
    n = 4 ^ a * t := hn'
    _ = 4 ^ a * (8 * (t / 8) + 7) := by
          -- Apply `ht_eq` under multiplication (avoid rewriting `t` inside `t/8`).
          simpa using congrArg (fun r : ℕ => 4 ^ a * r) ht_eq

/-- Necessary condition: representation as a sum of three squares implies n is not an exception. -/
