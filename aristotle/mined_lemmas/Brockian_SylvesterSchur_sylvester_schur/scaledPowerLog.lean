import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

noncomputable def scaledPowerLog (x y : ℝ) : ℝ :=
  log x + √y * log y - x * log (y / (2 * x))

