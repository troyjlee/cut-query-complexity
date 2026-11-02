import numpy as np; from lw import *; from t4helper import build
for r in [100,160]:
  best=(0,)
  for s in [0.3,0.1,0.05]:
    for t_id in [0.3,0.1,0.03]:
      A=build(r,s,1.0,t_id); m=A.shape[0]; L0=L0of(m); p=1-1/L0
      w=lewis(A,p,iters=3000,tol=1e-10); q=cs(A,w+2*r/m)
      if q>best[0]: best=(q,cs(A,w),m,s,t_id,2*m**(1-p))
  print(r,best,flush=True)
