import numpy as np
from scipy import stats

def sieve(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

rng = np.random.default_rng(12345)
N=50_000_000
primes=sieve(N); primes=primes[primes>5]
r=(primes%5).astype(np.int64)
M=len(r)

# ---- observed 1-step transition matrix on states {1,2,3,4} ----
idx={1:0,2:1,3:2,4:3}; inv={v:k for k,v in idx.items()}
ai=np.array([idx[x] for x in r]);
T=np.zeros((4,4))
for i in range(4):
    row=ai[1:][ai[:-1]==i]
    T[i]=np.bincount(row,minlength=4)/len(row)
pi=np.bincount(ai,minlength=4)/M   # stationary marginal (~uniform)

def markov_seq(n, T, pi, rng):
    states=np.empty(n,dtype=np.int64)
    states[0]=rng.choice(4,p=pi)
    # vectorized-ish sampling
    u=rng.random(n)
    cdf=np.cumsum(T,axis=1)
    s=states[0]
    for t in range(1,n):
        s=np.searchsorted(cdf[s],u[t]); states[t]=s
    return states

def iid_seq(n, pi, rng):
    return rng.choice(4,size=n,p=pi)

def holonomy_stats(states):
    """states = residue-index array. Non-overlapping windows of 5.
       H = (sum of residues) mod 5 ; D = # consecutive repeats within window."""
    m=(len(states)//5)*5
    w=states[:m].reshape(-1,5)
    res=np.array([inv[i] for i in range(4)])[w]   # actual residues {1,2,3,4}
    H=res.sum(axis=1)%5
    D=(w[:,1:]==w[:,:-1]).sum(axis=1)             # repeats per window (phase-depth)
    return H,D

def chi2(obs_counts, exp_counts):
    e=exp_counts*obs_counts.sum()/exp_counts.sum()
    mask=e>0
    return stats.chisquare(obs_counts[mask], e[mask])

# real
Hr,Dr=holonomy_stats(ai)
# nulls (match length)
Ha,Da=holonomy_stats(iid_seq(M,pi,rng))
Hb,Db=holonomy_stats(markov_seq(M,T,pi,rng))

def dist(x,k): return np.bincount(x,minlength=k)

print("=== (Q1) Holonomy H = sum(window residues) mod 5 : distribution over 5 classes ===")
for name,H in [("REAL",Hr),("NULL-A iid",Ha),("NULL-B Markov",Hb)]:
    d=dist(H,5); print(f"  {name:14} {d/d.sum()}")
print("  chi2 REAL vs NULL-A(iid):   ", chi2(dist(Hr,5),dist(Ha,5)))
print("  chi2 REAL vs NULL-B(Markov):", chi2(dist(Hr,5),dist(Hb,5)))

print("\n=== phase-depth D = #repeats in window (0..4) ===")
for name,D in [("REAL",Dr),("NULL-A iid",Da),("NULL-B Markov",Db)]:
    d=dist(D,5); print(f"  {name:14} {d/d.sum()}   mean={D.mean():.4f}")
print("  chi2 REAL vs NULL-A(iid):   ", chi2(dist(Dr,5),dist(Da,5)))
print("  chi2 REAL vs NULL-B(Markov):", chi2(dist(Dr,5),dist(Db,5)))

print("\n=== (Q2) orientation symmetry: reverse each window, recompute H ===")
m=(M//5)*5; wr=ai[:m].reshape(-1,5)[:, ::-1].reshape(-1)
Hrev,_=holonomy_stats(ai[:m][::-1])   # full reverse
print("  H(real) vs H(fully-reversed sequence) chi2:", chi2(dist(Hr,5),dist(Hrev,5)))
