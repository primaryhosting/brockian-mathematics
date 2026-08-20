import Mathlib
open Finset
namespace C2.IT3

/-- Each entropy term `-p log p` is nonnegative on `[0,1]`. -/

theorem shannon_two (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    0 < -p*Real.log p - (1-p)*Real.log (1-p) := by
  have hlp : Real.log p < 0 := Real.log_neg h0 h1
  have hlq : Real.log (1-p) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith

/-- Midpoint concavity of `log`, equivalently the AM–GM inequality. -/
