import Mathlib
namespace Frontier.CryptoComplexity
open Function

/-- The one-time pad map `k ↦ m ^^^ k` is a bijection, since it is an involution. -/

theorem otp_bijective (n : ℕ) (m : BitVec n) : Bijective (fun k : BitVec n => m ^^^ k) := by
  refine Function.Involutive.bijective (fun k => ?_)
  show m ^^^ (m ^^^ k) = k
  rw [← BitVec.xor_assoc]
  simp

/-- Pigeonhole: a map into a strictly smaller finite type cannot be injective. -/
