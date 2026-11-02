import numpy as np; from lw import *
def build(n,K,s):
    m=K+1+(n-1); A=np.zeros((m,n))
    A[0,0]=1.0; A[1:K+1,0]=s
    for d in range(1,n): A[K+d,d]=1.0
    return A
for (n,K) in [(10,200),(30,1000),(50,1000),(60,3600),(100,10000)]:
    m=K+n; L0=L0of(m); p=1-1/L0; best=None
    for R in [2,5,10,20,40,80,160,320]:
        s=(R/K)**(1/p); A=build(n,K,s); w=lewis(A,p)
        for name,c0 in [('unreg',0),('LS',n/(2*m)),('note',2*n/m)]:
            q=cs(A,w+c0)
            if best is None or q>best.get(name,(0,))[0]: best=best or {}; best[name]=(round(q,3),R)
    print(n,K,m,'p=',round(p,4),'2m^(1-p)=',round(2*m**(1-p),3),best,flush=True)
