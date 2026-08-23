import numpy as np, itertools
from scipy import stats
def sieve(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
N=100_000_000
primes=sieve(N); primes=primes[primes>5]
idx={1:0,2:1,3:2,4:3}; inv=np.array([1,2,3,4])
ai=np.array([idx[x] for x in (primes%5)]); M=len(ai)

# empirical k-th order Markov transition (order = # of conditioning states)
def kth_order_null_D(order):
    # P(next | previous `order` states); stationary weights from (order)-gram freq
    from collections import defaultdict
    # build conditional counts
    cond=defaultdict(lambda: np.zeros(4)); start=defaultdict(float)
    for t in range(order, M):
        ctx=tuple(ai[t-order:t]); cond[ctx][ai[t]]+=1
    for ctx in cond: cond[ctx]/=cond[ctx].sum()
    # start (order)-gram stationary distribution
    for t in range(order-1, M):
        start[tuple(ai[t-order+1:t+1])]+=1
    tot=sum(start.values());
    for k in start: start[k]/=tot
    # exact 5-window repeat distribution under this order-Markov
    Dn=np.zeros(5)
    for path in itertools.product(range(4),repeat=5):
        if order==1: w=start[(path[0],)] if (path[0],) in start else 0.0
        else:
            w=start[tuple(path[:order])] if tuple(path[:order]) in start else 0.0
        ok=w>0
        for t in range(order,5):
            ctx=tuple(path[t-order:t])
            if ctx in cond: w*=cond[ctx][path[t]]
            else: w=0.0; break
        D=sum(1 for a,b in zip(path[:-1],path[1:]) if a==b); Dn[D]+=w
    return Dn/Dn.sum()

m=(M//5)*5; W=ai[:m].reshape(-1,5)
Dr=np.bincount((W[:,1:]==W[:,:-1]).sum(axis=1),minlength=5); nW=Dr.sum()
preal=Dr/nW
def chi2(obs,p):
    e=p*obs.sum(); mask=e>1
    st=(((obs-e)**2/e)[mask]).sum(); return st, stats.chi2.sf(st,mask.sum()-1)
print(f"windows={nW:,}   REAL D dist = {np.round(preal,5)}")
print("\nHow much of the phase-depth deviation survives as we match higher-order residue correlations:")
print(f"{'null order':>12} {'TV(real,null)':>14} {'chi2':>12} {'p':>12}")
for order in (1,2,3,4):
    pn=kth_order_null_D(order); tv=0.5*np.abs(preal-pn).sum(); st,p=chi2(Dr,pn)
    print(f"{order:>12} {tv:>14.6f} {st:>12.1f} {p:>12.2e}")
print("\n(order-1 = pairwise/Fourier-level ; higher orders match longer residue correlations)")
