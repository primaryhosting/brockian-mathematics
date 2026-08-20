/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires the `import` lines to precede every command, including module
-- docstrings, so the header above is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

`Brockian.GoldbachWheelK2_947` extends the `GoldbachWheelK2` family to the wheel
modulus `947`: every even number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two
primes (`K = 2` summands).

Mathlib contains no Goldbach-type theorem to appeal to (the Goldbach conjecture is
open), so the finite range covered by this wheel is verified by an explicit
certificate:

* `gwPrimes947` is the list of all primes below `1894`; each entry is checked with
  the `Nat.Prime` extension of `norm_num` in `gwPrimes947_prime`.
* `gwWit947 i` is the least prime `p` for which `(4 + 2 * i) - p` is prime; the
  data is stored in `gwWitChunks947`.
* `gwCert947` checks, by kernel evaluation (`decide`), that for every `i < 946`
  both `gwWit947 i` and `4 + 2 * i - gwWit947 i` occur in `gwPrimes947`.
-/

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false

namespace Brockian

/-- All prime numbers below `2 * 947 = 1894`. -/

def gwPrimes947 : List Nat :=
[
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
  97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
  193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
  307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
  421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
  547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
  659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
  797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
  929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033,
  1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
  1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
  1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367,
  1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481,
  1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
  1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693,
  1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
  1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889
]

/-- Every entry of `gwPrimes947` is prime. -/
