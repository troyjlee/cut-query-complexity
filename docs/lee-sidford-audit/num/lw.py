import numpy as np
def lewis(A,p,iters=3000,tol=1e-14):
    m,n=A.shape; w=np.ones(m)*n/m
    for _ in range(iters):
        M=A.T@(w[:,None]**(1-2/p)*A)
        Mi=np.linalg.inv(M)
        lev=np.einsum('ij,jk,ik->i',A,Mi,A)
        wn=lev**(p/2)
        if np.max(np.abs(np.log(wn)-np.log(w)))<tol: w=wn;break
        w=wn
    return w
def cs(A,g):
    Mi=np.linalg.inv(A.T@(A/g[:,None]))
    return np.max(np.einsum('ij,jk,ik->i',A,Mi,A)/g**2)
def L0of(m):
    lb=max(2,int(np.ceil(np.log2(4*m)))); L=1
    while L<lb: L*=2
    return L
