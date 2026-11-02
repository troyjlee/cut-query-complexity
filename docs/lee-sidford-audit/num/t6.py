import numpy as np; from lw import *; from blk import build
rng=np.random.default_rng(5)
worst=0
for (n,K) in [(10,200),(50,1000),(100,10000)]:
    m=K+n; p=1-1/L0of(m)
    for R in [2,5,10,20,40,80,160,320,1000]:
        s=(R/K)**(1/p); A=build(n,K,s); w=lewis(A,p)
        worst=max(worst,cs(A,w+1/(2*m)))
for t in range(1500):
    m=int(rng.integers(3,60)); n=int(rng.integers(1,min(m,10)+1))
    A=rng.standard_normal((m,n))*np.exp(4*rng.standard_normal((m,1)))
    if np.linalg.matrix_rank(A)<n: continue
    p=1-1/L0of(m); w=lewis(A,p); worst=max(worst,cs(A,w+1/(2*m)))
print('max c_s with c0=1/(2M):',worst,'(proved bound 16)')
