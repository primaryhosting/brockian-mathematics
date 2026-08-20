import Mathlib
namespace Brockian.MsHeron
/-- Heron's formula (algebraic form): 16·Area² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴, where
    a,b,c are side lengths and Area = ½|det(B−A, C−A)| for A,B,C ∈ ℝ². -/
theorem heron (A B C : ℝ × ℝ) :
    let a := dist B C; let b := dist C A; let c := dist A B
    let area := |(B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)| / 2
    16 * area ^ 2 = 2*a^2*b^2 + 2*b^2*c^2 + 2*c^2*a^2 - a^4 - b^4 - c^4 := by
  sorry
end Brockian.MsHeron
