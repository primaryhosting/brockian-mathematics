import Mathlib
namespace C2.Crypto2

/-- The one-time pad encryption map `k ↦ m ^^^ k` is a bijection on `BitVec n`,
since XOR-ing with a fixed mask is an involution. -/

theorem otp_bij (n : ℕ) (m : BitVec n) : Function.Bijective (fun k : BitVec n => m ^^^ k) := by
  have hinv : Function.Involutive (fun k : BitVec n => m ^^^ k) := by
    intro k
    simp only
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  exact hinv.bijective

/-- RSA correctness: if `e * d ≡ 1 [MOD φ n]` and `m` is coprime to `n`, then
decryption inverts encryption, i.e. `(m ^ e) ^ d ≡ m [MOD n]`. -/
