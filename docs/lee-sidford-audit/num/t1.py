import numpy as np; from lw import *
rng=np.random.default_rng(0); worst={}
for trial in range(3000):
    m=int(rng.integers(3,40)); n=int(rng.integers(1,min(m,8)+1))
    kind=trial%4
    if kind==0: A=rng.standard_normal((m,n))
    elif kind==1: A=rng.standard_normal((m,n))*np.exp(3*rng.standard_normal((m,1)))
    elif kind==2:
        A=np.zeros((m,n)); 
        for i in range(m): A[i,rng.integers(n)]=1; 
        A[:n]=np.eye(n); A+=1e-3*rng.standard_normal((m,n))*rng.integers(0,2,(m,1))
    else:
        A=rng.standard_normal((m,n)); A[:m-n]*=1e-3*rng.random((m-n,1)); 
    if np.linalg.matrix_rank(A)<n: continue
    L0=L0of(m); p=1-1/L0
    w=lewis(A,p)
    for name,c0 in [('unreg',0.0),('LS n/2m',n/(2*m)),('note 2n/m',2*n/m)]:
        v=cs(A,w+c0); 
        if v>worst.get(name,(0,))[0]: worst[name]=(v,m,n,kind, 2*m**(1-p))
print(worst)
