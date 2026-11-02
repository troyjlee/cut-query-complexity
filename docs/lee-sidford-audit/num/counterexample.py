# Counterexample to LS (arXiv 1910.08033v2) Theorem 29 sensitivity claim c_s(g) <= 2 m^{1-p}
# for g = w_p(A) + c0, c0 > 0.  Block matrix: column 1 has one unit row and K rows of size s;
# columns 2..n have one unit row each.
import numpy as np; from lw import lewis, cs, L0of; from blk import build
n,K,R=100,10000,80
m=K+n; L0=L0of(m); p=1-1/L0; s=(R/K)**(1/p)
A=build(n,K,s); w=lewis(A,p,iters=5000,tol=1e-15)
M=A.T@(w[:,None]**(1-2/p)*A); lev=w**(1-2/p)*np.einsum('ij,jk,ik->i',A,np.linalg.inv(M),A)
print('m',m,'n',n,'L0',L0,'p',p,'s',s)
print('Lewis fixed-point residual max|w-lev|/w =',np.max(np.abs(w-lev)/w),' sum w =',w.sum())
print('w[row0] =',w[0],' w[small rows] =',w[1],' c0_LS =',n/(2*m),' c0_note =',2*n/m)
print('c_s(unregularized) =',cs(A,w),'  claimed bound 2m^(1-p) =',2*m**(1-p))
print('c_s(g=w+n/(2m))   =',cs(A,w+n/(2*m)))
print('c_s(g=w+2n/m)     =',cs(A,w+2*n/m))
print('c_s(g=w+1/(2m))   =',cs(A,w+1/(2*m)),' (repaired regularization; proved bound 16)')
