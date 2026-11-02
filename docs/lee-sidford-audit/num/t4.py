import numpy as np, itertools; from lw import *
# incidence-type LP rows: +I_r rows and e_u - e_v edge rows (complete graph), arbitrary positive row scalings (= S(x)^{-1})
def build(r,s_star,t_other,t_id):
    rows=[];sc=[]
    for v in range(r):
        e=np.zeros(r);e[v]=1;rows.append(e);sc.append(1.0 if v==0 else t_id)
    for u,v in itertools.combinations(range(r),2):
        e=np.zeros(r);e[u]=1;e[v]=-1;rows.append(e);sc.append(s_star if u==0 else t_other)
    return np.array(rows)*np.array(sc)[:,None]
best=(0,)
for r in [20,40,60]:
  for s in [1e-1,3e-2,1e-2,3e-3,1e-3]:
    for t_other in [1e-3,1e-2,1e-1,1]:
      for t_id in [1e-3,1e-1,1]:
        A=build(r,s,t_other,t_id); m=A.shape[0]; L0=L0of(m); p=1-1/L0
        w=lewis(A,p,iters=4000,tol=1e-12)
        q=cs(A,w+2*r/m); qu=cs(A,w)
        if q>best[0]: best=(q,qu,r,m,s,t_other,t_id)
  print(r,best,flush=True)
