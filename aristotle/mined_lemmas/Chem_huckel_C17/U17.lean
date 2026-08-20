import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

noncomputable def U17 : Matrix (ZMod 17) (ZMod 17) ℂ := fun j k => ee (j * k)

/-- Inverse discrete Fourier transform matrix. -/
