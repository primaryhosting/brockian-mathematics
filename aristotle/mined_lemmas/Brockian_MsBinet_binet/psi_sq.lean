import Mathlib
namespace Brockian.MsBinet


private lemma psi_sq : ((1 - Real.sqrt 5) / 2) ^ 2 = ((1 - Real.sqrt 5) / 2) + 1 := by
  have h := sq_sqrt5
  field_simp
  nlinarith [h]

