import Mathlib
namespace C2.Crypto2

/-- The one-time pad encryption map `k ↦ m ^^^ k` is a bijection on `BitVec n`,
since XOR-ing with a fixed mask is an involution. -/

theorem xor_self (n : ℕ) (a : BitVec n) : a ^^^ a = 0 := BitVec.xor_self

end C2.Crypto2

