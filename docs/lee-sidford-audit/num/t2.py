import numpy as np; from lw import *; from scipy.optimize import minimize
rng=np.random.default_rng(1)
res={}
for (m,n) in [(4,2),(6,2),(6,3),(8,2),(8,3),(10,3),(12,4),(16,3)]:
  L0=L0of(m); p=1-1/L0
  for name,cf in [('unreg',0),('LS',0.5),('note',2.0)]:
    best=0
    for start in range(6):
      x0=rng.standard_normal(m*n)
      def f(x):
        A=x.reshape(m,n)
        if np.linalg.matrix_rank(A)<n or np.min(np.linalg.norm(A,axis=1))<1e-8: return 0
        try:
          w=lewis(A,p,iters=500,tol=1e-11); return -cs(A,w+cf*n/m)
        except Exception: return 0
      r=minimize(f,x0,method='Nelder-Mead',options={'maxiter':3000,'xatol':1e-8,'fatol':1e-10})
      best=max(best,-r.fun)
    res[(m,n,name)]=(round(best,4), round(2*m**(1-p),4))
    print((m,n,name),res[(m,n,name)],flush=True)
