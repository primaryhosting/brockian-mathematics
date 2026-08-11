"""W3: the closed-form dual certificate for level C0+I5 (and every superset),
30-dps arithmetic.  This is the certificate that does the real work in
Ordering B, and it is INDEPENDENT of band/cone/channel rows -- hence robust
to I3's extra adversary variables and to every grid/tol/window choice.

CERTIFICATE (nonnegative combination of the level's constraints):
   1 x [I5 row]      3 psi_1 + 4 (sum_{m>=2} psi_m + sum_y p_y) >= 4 - 1/c1*
  -2 x [count row]   psi_1 + sum_{m>=2} m psi_m + 2 sum_y p_y  = 1
  +  sum_{m>=2} (2m - 4) x [psi_m >= 0]
  ---------------------------------------------------------------
   psi_1  >=  (4 - 1/c1*) - 2 + sum_{m>=2} (2m-4) psi_m  >=  2 - 1/c1*.

Every multiplier is >= 0 where required ((2m-4) >= 0 for m >= 2); the
equality row's multiplier is free.  Machine verification below expands the
combination symbolically over the variable vector and checks coefficient
identities exactly (as rationals in the single transcendental 1/c1*).

MATCHING WITNESS at the same value: the grid LP (ladder.py L1B) returns
psi_1 = 0.6725007 exactly at XF=80/na=600/tol=2e-4 with a mixed
doubles+shallow-pairs configuration saturating the I5 row -- so C0+I5 is
SETTLED both sides at 2 - 1/c1* = 0.6725007 up to the witness's tol.
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 30
c1 = 2 * mp.tan(1 / mp.sqrt(2)) / (mp.sqrt(2) + mp.tan(1 / mp.sqrt(2)))
RHS = 4 - 1 / c1
VA = 2 - 1 / c1
MMAX = 5

print("== constants (30 dps) ==")
print(f"   c1* = {mp.nstr(c1, 15)}")
print(f"   I5 RHS 4 - 1/c1* = {mp.nstr(RHS, 15)}")
print(f"   V_A  2 - 1/c1*  = {mp.nstr(VA, 15)}")

# symbolic check over variables [psi_1..psi_5, p_1..p_5]
# rows as coefficient vectors; constraint sense: row . x >= rhs (I5),
# row . x = 1 (count), x_j >= 0.
i5 = np.array([3, 4, 4, 4, 4] + [4] * 5, dtype=object)
count = np.array([1, 2, 3, 4, 5] + [2] * 5, dtype=object)
target = np.zeros(10, dtype=object); target[0] = 1          # psi_1
comb = i5 - 2 * count
# comb = psi_1*(3-2) + psi_m*(4-2m) + p*(4-4) = psi_1 + sum (4-2m) psi_m
expected = np.array([1, 0, -2, -4, -6] + [0] * 5, dtype=object)
assert np.all(comb == expected), comb
slack_mult = np.array([0, 0, 2, 4, 6] + [0] * 5, dtype=object)  # (2m-4)+ on psi
final = comb + slack_mult
assert np.all(final == target), final
print("\n== symbolic combination check ==")
print(f"   1*(I5) - 2*(count) + sum (2m-4)*(psi_m>=0)  ==  psi_1   EXACT")
print(f"   all inequality multipliers nonnegative: "
      f"{all(m >= 0 for m in [1] + list(slack_mult))}")
print(f"   => psi_1 >= (4 - 1/c1*) - 2*1 = 2 - 1/c1* = {mp.nstr(VA, 12)}")
print("\n   Scope: uses ONLY the I5 row, the count row and psi >= 0 --")
print("   valid at every grid, every tol, every Bochner window, with or")
print("   without the pair-pair channel (I3), tied or untied.")
