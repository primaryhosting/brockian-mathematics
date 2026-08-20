import Mathlib
namespace Frontier.BrockianSieveDeep

theorem nu_singleton_lt (a p : ℕ) (hp : 2 ≤ p) : nu {a} p < p := by
  have : nu {a} p ≤ 1 := by simpa using nu_le_card {a} p
  omega

end Frontier.BrockianSieveDeep

