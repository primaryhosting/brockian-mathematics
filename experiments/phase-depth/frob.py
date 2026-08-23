import numpy as np
# distinct-degree factorization -> cycle type (partition of 5) of Frobenius at p, via
# gcd(f, x^{p^d}-x) chain. Pure-python, fast for degree 5.
def sieve(n):
    s=np.ones(n+1,dtype=bool); s[:2]=False
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0].tolist()

def polymulmod(a,b,f,p):
    # a,b,f lists low->high; f monic degree df
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                r[i+j]=(r[i+j]+ai*bj)%p
    return polymod(r,f,p)
def polymod(a,f,p):
    a=a[:]; df=len(f)-1
    for i in range(len(a)-1,df-1,-1):
        if a[i]:
            c=a[i]
            for j in range(df+1):
                a[i-df+j]=(a[i-df+j]-c*f[j])%p
    return [x%p for x in a[:df]] or [0]
def polypowmod(base,e,f,p):  # base^e mod f mod p
    result=[1]; b=base[:]
    while e:
        if e&1: result=polymulmod(result,b,f,p)
        b=polymulmod(b,b,f,p); e>>=1
    return result
def polygcd(a,b,p):
    a=[x%p for x in a]; b=[x%p for x in b]
    def deg(x):
        d=len(x)-1
        while d>0 and x[d]==0: d-=1
        return d
    def trim(x):
        d=deg(x); return x[:d+1]
    a=trim(a); b=trim(b)
    while not(len(b)==1 and b[0]==0):
        # a mod b
        a=trim(a); b=trim(b)
        db=deg(b); inv=pow(b[db],p-2,p)
        r=a[:]
        for i in range(deg(r),db-1,-1):
            if i<len(r) and r[i]:
                c=r[i]*inv%p
                for j in range(db+1):
                    r[i-db+j]=(r[i-db+j]-c*b[j])%p
        r=trim(r); a,b=b,r
    return trim(a)

def cycle_type(fint,p):
    # f as int coeffs low->high, monic degree 5. Return sorted partition of 5 (Frobenius cycle type),
    # or None if p ramifies (repeated factor) — detect via gcd(f,f').
    f=[c%p for c in fint]
    # squarefree check
    fp=[(i*f[i])%p for i in range(1,len(f))]
    if len(fp)==0: return None
    g=polygcd(f,fp,p)
    if len(g)>1: return None  # ramified
    x=[0,1]
    # distinct degree factorization
    typ=[]; fcur=f[:]; 
    def deg(x):
        d=len(x)-1
        while d>0 and x[d]==0: d-=1
        return d
    d=1; xp=polypowmod(x,p,fcur,p)  # x^p mod f
    cur=xp
    while deg(fcur)>0 and d<=5:
        # gcd(fcur, x^{p^d}-x)
        h=cur[:]; 
        if len(h)<2: h=h+[0]
        h[1]=(h[1]-1)%p  # cur - x
        g=polygcd(fcur,h,p)
        dg=deg(g)
        if dg>0:
            nfac=dg//d
            typ+=[d]*nfac
            # divide fcur by g
            # polynomial division fcur/g
            q=fcur[:]; 
            # do exact division
            from math import inf
            num=fcur[:]; den=g[:]
            def polydiv(num,den,p):
                num=num[:]; dd=deg(den); inv=pow(den[dd],p-2,p); q=[0]*(deg(num)-dd+1)
                for i in range(deg(num),dd-1,-1):
                    if i-dd<0: break
                    c=num[i]*inv%p; q[i-dd]=c
                    for j in range(dd+1):
                        num[i-dd+j]=(num[i-dd+j]-c*den[j])%p
                return q
            fcur=polydiv(fcur,g,p)
        d+=1
        if deg(fcur)>0:
            cur=polypowmod(cur,p,fcur,p) if False else polypowmod(x,p,fcur,p)
            for _ in range(d-1):
                cur=polypowmod(cur,p,fcur,p)
    return tuple(sorted(typ)) if sum(typ)==5 else None

# candidate quintics (low->high coeffs), monic
cands = {
 "x^5 - x - 1 (expect S5)":        [-1,-1,0,0,0,1],
 "x^5 - 5x + 12 (test D5)":        [12,-5,0,0,0,1],
 "x^5+x^4-4x^3-3x^2+3x+1 (C5?)":  [1,3,-3,-4,1,1],
 "x^5 - 2 (expect F20)":           [-2,0,0,0,0,1],
}
from collections import Counter
primes=sieve(200000)
for name,f in cands.items():
    c=Counter()
    for p in primes:
        if p< 13: continue
        t=cycle_type(f,p)
        if t: c[t]+=1
    tot=sum(c.values())
    dens={str(k):round(v/tot,3) for k,v in sorted(c.items())}
    print(f"{name:32} n={tot}  densities={dens}")
print("\nGalois signatures (cycle-type densities): C5={(1,1,1,1,1):.2,(5):.8}; D5={1^5:.1,5:.4,2^2 1:.5}; S5=7 types; F20 has (1,4)&(1,2,2) etc.")
