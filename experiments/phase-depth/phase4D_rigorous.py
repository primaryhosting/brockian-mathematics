import numpy as np, itertools
from scipy import stats
from sympy import Poly, symbols, primerange
x=symbols('x')

def frob_seq(coeffs, PMAX):
    seq=[]
    for p in primerange(17,PMAX):
        try: fl=Poly(coeffs,x,modulus=p).factor_list()[1]
        except Exception: continue
        if any(m>1 for _,m in fl): continue
        t=tuple(sorted(g.degree() for g,_ in fl))
        if sum(t)==5: seq.append(t)
    alpha=sorted(set(seq)); code={t:i for i,t in enumerate(alpha)}
    return np.array([code[t] for t in seq]), alpha

def residue_seq(PMAX,q=5):
    r=np.array([p%q for p in primerange(7,PMAX)])
    u=sorted(set(r.tolist())); code={v:i for i,v in enumerate(u)}
    return np.array([code[v] for v in r]), u

def kth_null_probs(train, K, A, w=5):
    from collections import defaultdict
    cond=defaultdict(lambda: np.zeros(A)); start=defaultdict(float)
    for t in range(K,len(train)): cond[tuple(train[t-K:t])][train[t]]+=1
    for k in cond: cond[k]=cond[k]/cond[k].sum()
    for t in range(K-1,len(train)): start[tuple(train[t-K+1:t+1])]+=1
    tot=sum(start.values())
    for k in start: start[k]/=tot
    Dn=np.zeros(w)
    for path in itertools.product(range(A),repeat=w):
        ww=start.get(tuple(path[:K]),0.0)
        for t in range(K,w):
            c=cond.get(tuple(path[t-K:t])); ww=ww*c[path[t]] if c is not None else 0.0
        D=sum(1 for a,b in zip(path[:-1],path[1:]) if a==b); Dn[D]+=ww
    return Dn/max(Dn.sum(),1e-12)

def analyze(name, sym, A):
    # split into train (fit null) / test (evaluate) by even/odd window blocks
    m=(len(sym)//5)*5; W=sym[:m].reshape(-1,5)
    ntr=len(W)//2
    train=W[:ntr].reshape(-1); test=W[ntr:]
    Dtest=np.bincount((test[:,1:]==test[:,:-1]).sum(axis=1),minlength=5)
    ptest=Dtest/Dtest.sum()
    row=f"{name:26}{A:>4}{len(W):>9}"
    for K in (1,2,3):
        pn=kth_null_probs(train,K,A)
        tv=0.5*np.abs(ptest-pn).sum()
        e=pn*Dtest.sum(); mask=e>5
        chi=(((Dtest-e)**2/e)[mask]).sum(); p=stats.chi2.sf(chi,max(mask.sum()-1,1))
        row+=f"  | k={K}: TV={tv:.5f} p={p:.1e}"
    return row

PMAX=10_000_000
POLYS={"D5":[1,-1,-5,4,3,-1],"S5":[1,0,0,0,-1,-1]}
lines=[f"train/test split; null fit on train, chi2/TV on test.  PMAX={PMAX}"]
# abelian baselines (fast, large N)
rs,ru=residue_seq(50_000_000,5); lines.append(analyze("residue mod 5",rs,len(ru)))
c5,c5a=residue_seq(50_000_000,11);  # C5 Frobenius ~ p mod 11
lines.append(analyze("C5 (p mod 11)",c5,len(c5a)))
for nm,c in POLYS.items():
    sym,alpha=frob_seq(c,PMAX); lines.append(analyze(nm,sym,len(alpha)))
res="\n".join(lines); print(res); open("phase4D_rigorous.txt","w").write(res)
