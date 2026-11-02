import numpy as np, itertools; from lw import *
# incidence-type LP rows: +I_r rows and e_u - e_v edge rows (complete graph), arbitrary positive row scalings (= S(x)^{-1})
def build(r,s_star,t_other,t_id):
    rows=[];sc=[]
    for v in range(r):
        e=np.zeros(r);e[v]=1;rows.append(e);sc.append(1.0 if v==0 else t_id)
    for u,v in itertools.combinations(range(r),2):
        e=np.zeros(r);e[u]=1;e[v]=-1;rows.append(e);sc.append(s_star if u==0 else t_other)
    return np.array(rows)*np.array(sc)[:,None]
