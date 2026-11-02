import numpy as np
def build(n,K,s):
    m=K+1+(n-1); A=np.zeros((m,n))
    A[0,0]=1.0; A[1:K+1,0]=s
    for d in range(1,n): A[K+d,d]=1.0
    return A
