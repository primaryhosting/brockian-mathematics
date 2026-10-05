import numpy as np, itertools
from scipy import stats

def sieve(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

N=100_000_000
primes=sieve(N); primes=primes[primes>5]
r=(primes%5).astype(np.int64)
idx={1:0,2:1,3:2,4:3}; inv=np.array([1,2,3,4])
ai=np.array([idx[x] for x in r]); M=len(ai)
print(f"primes in (5,{N}]: {M:,}")

# exact stationary 1-step Markov model (matches ALL marginal+pairwise residue statistics)
T=np.zeros((4,4))
for i in range(4):
    row=ai[1:][ai[:-1]==i]; T[i]=np.bincount(row,minlength=4)/len(row)
pi=np.bincount(ai,minlength=4)/M

# EXACT null distribution of window statistics under the pairwise Markov model:
# enumerate all 4^5 residue paths, weight by pi[s0]*prod T.
Dnull=np.zeros(5); Hnull=np.zeros(5)
for path in itertools.product(range(4),repeat=5):
    w=pi[path[0]]
    for a,b in zip(path[:-1],path[1:]): w*=T[a,b]
    D=sum(1 for a,b in zip(path[:-1],path[1:]) if a==b)
    H=int(inv[list(path)].sum()%5)
    Dnull[D]+=w; Hnull[H]+=w

# REAL empirical (non-overlapping windows)
m=(M//5)*5; W=ai[:m].reshape(-1,5); nW=len(W)
Dreal=(W[:,1:]==W[:,:-1]).sum(axis=1)
Hreal=(inv[W].sum(axis=1))%5
Dr=np.bincount(Dreal,minlength=5); Hr=np.bincount(Hreal,minlength=5)

def chi2_vs_exact(obs, p_null):
    e=p_null*obs.sum(); mask=e>1
    st=(((obs-e)**2/e)[mask]).sum(); dof=mask.sum()-1
    return st, dof, stats.chi2.sf(st,dof)

print(f"\nwindows: {nW:,}   (df for chi2 tests below)")
print("\n=== phase-depth D=#repeats: REAL vs EXACT pairwise-Markov null ===")
print("  null p:", np.round(Dnull,5))
print("  real p:", np.round(Dr/Dr.sum(),5))
st,dof,p=chi2_vs_exact(Dr,Dnull); print(f"  chi2={st:.1f} dof={dof} p={p:.3e}")
# effect size: total variation distance
tv=0.5*np.abs(Dr/Dr.sum()-Dnull).sum(); print(f"  total-variation distance = {tv:.5f}")

print("\n=== holonomy H=sum mod5: REAL vs EXACT pairwise-Markov null ===")
print("  null p:", np.round(Hnull,5))
print("  real p:", np.round(Hr/Hr.sum(),5))
st,dof,p=chi2_vs_exact(Hr,Hnull); print(f"  chi2={st:.1f} dof={dof} p={p:.3e}")
tv=0.5*np.abs(Hr/Hr.sum()-Hnull).sum(); print(f"  total-variation distance = {tv:.5f}")

# Control: does a 2-step (pairwise+triple) Markov absorb the deviation? Compare real D
# to the EXACT prediction of a 2nd-order Markov (matches all TRIPLE statistics).
T2={}  # (a,b)->dist over c
A2=ai
for a in range(4):
  for b in range(4):
    m3=A2[2:][(A2[:-2]==a)&(A2[1:-1]==b)]
    T2[(a,b)]=np.bincount(m3,minlength=4)/max(len(m3),1)
pi2=np.zeros((4,4))
for a in range(4):
  for b in range(4):
    pi2[a,b]=((A2[:-1]==a)&(A2[1:]==b)).mean()
Dnull2=np.zeros(5)
for path in itertools.product(range(4),repeat=5):
    w=pi2[path[0],path[1]]
    for a,b,c in zip(path[:-2],path[1:-1],path[2:]): w*=T2[(a,b)][c]
    D=sum(1 for x,y in zip(path[:-1],path[1:]) if x==y); Dnull2[D]+=w
st,dof,p=chi2_vs_exact(Dr,Dnull2)
print("\n=== CONTROL: REAL D vs EXACT 2nd-order (triple-matched) Markov null ===")
print("  null2 p:", np.round(Dnull2,5), "  real p:", np.round(Dr/Dr.sum(),5))
print(f"  chi2={st:.1f} dof={dof} p={p:.3e}   TV={0.5*np.abs(Dr/Dr.sum()-Dnull2).sum():.5f}")
