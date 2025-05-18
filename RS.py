import galois
import numpy as np
import random
import matplotlib.pyplot as plt
from scipy import stats

#defines RS code (q;n,k,d)
s=4
p=2 #p must be a prime number
q=p**s
n=q-1
d=7 #d must be odd and <=q-1
k=q-d

#basic verifications
if not(1<d<q): raise Exception("d must be strictly between 1 and {}!".format(q))
if (n-k)%2 != 0: raise Exception("n-k should be even!")
if s<=0 or p<=1 or d<=1 or k<=0: raise Exception("all parameters should be > 0!")

#defining our finite fields
F1 = galois.GF(p,s)

#polynomials related operations in GF
def get(F, P, i):
   try:
       return P[i]
   except IndexError:
       return F(0)

def poly_add(F,P,Q):
    R=[]
    u=max(len(P),len(Q))
    for i in range(u):
        R.append(int(get(F,P,i)+get(F,Q,i)))
    return F(R)

def poly_mult(F, P,Q):
    R=[]
    u=len(P)+len(Q)-1
    for i in range(u):
        coef=F(0)
        for k in range(i+1):
            coef+=get(F,P,k)*get(F,Q,i-k)
        R.append(int(coef))
    return F(R)

def evaluate(F,P,a):
    result=F(0)
    for i in range(len(P)):
        result+=P[i]*(a**i)
    return result

def is_null(F,P):
    null=True
    for i in range(len(P)):
        if P[i] != F(0): null=False
    return null

def weight(F,P):
    w=0
    for i in range(len(P)):
        if P[i] != F(0): w+=1
    return w

def clean(F,P):
    index=-1
    while len(P)>=1 and (P[index]==F(0)):
        P=np.delete(P,index)
    return P

def deepcopy(F,L):
    C=[]
    for i in range(len(L)):
        C.append(int(L[i]))
    return F(C)

def DE(F,M,N):
    Q=F([0])
    R=deepcopy(F,M)
    N=clean(F,N)
    b=N[-1]**-1
    while len(R)>=len(N):
        u=len(R)-len(N)
        a=int(R[-1]*b)
        factor=[0]*u
        factor.append(a)
        Q=poly_add(F,Q,F(factor))
        R=poly_add(F,R,-poly_mult(F,F(factor),N))
        R=clean(F,R)
    return Q,R

def roots(F,P):
    R=[]
    for i in F.elements:
        if evaluate(F,P,i)==F(0): R.append(int(i))
    return F(R)

#finite field related operations
def least_primitive_root(F):
    for i in F.elements:
        count=2
        while (i**count != F(1)) and (i**count != i):
            count+=1
        if count==F.order-1: return i
    raise Exception("not prime")

def get_RS_generator(F):
    alpha=least_primitive_root(F)
    G=F([1])
    for i in range(1,d):
        G=poly_mult(F,G,F([-alpha**i,1]))
    return G

#coding and decoding operations
def coding(F, M):
    if len(M) != k : raise Exception("message must be of length {}!".format(k))
    mess = F(M)
    G=get_RS_generator(F)
    factor = [0]*(n-k)
    factor.append(1)
    A=poly_mult(F,mess,F(factor))
    _,B=DE(F,A,G)
    return poly_add(F,B,A)

def decoding(F,C):
    valid=True
    alpha=least_primitive_root(F)
    #tests if coded message is valid
    for i in range(1,d):
        if evaluate(F,C,alpha**i) != F(0): valid=False
    if valid:
        M=[]
        for i in range(n-k,n):
            M.append(int(C[i]))
        print("No error occured during transmission. Original message : {}".format(M))
        return F(M)
    else:
        #syndromes calculation
        S=[]
        for i in range(1,d):
            S.append(int(evaluate(F,C,alpha**i)))
        #initialisation of extended euclidean algorithm
        P=[]
        Q=[]
        A=[]
        B=[]
        #arrays initialization
        factor = [0]*(n-k)
        factor.append(1)
        P.append(F(factor))
        P.append(F(S))
        A.append(F([1]))
        A.append(F([0]))
        B.append(F([0]))
        B.append(F([1]))
        #arrays recursive calculation
        while not(is_null(F,P[-1])):
            q,r=DE(F,P[-2],P[-1])
            P.append(r)
            Q.append(q)
            A.append(poly_add(F,A[-2],-poly_mult(F,q,A[-1])))
            B.append(poly_add(F,B[-2],-poly_mult(F,q,B[-1])))
        #searching for the good P element
        index=0
        for i in range(1,len(P)):
            if len(P[i])-1<(n-k)/2 and len(P[i-1])-1>=(n-k)/2: index = i
        #syndrome polynomial
        b_0_inv=(evaluate(F,B[index],F(0)))**-1
        sigma=b_0_inv*B[index]
        x=(roots(F,sigma))**-1
        r=np.array(x.log(alpha), dtype=int) #here are stored the positions of errors scattered in our coded message
        r.sort() #reordering to mach the syndromes values
        f=len(r)
        x_final=[]
        for i in range(f):
            x_final.append(int(alpha**r[i]))
        #inverting Gauss system to find error values
        X_g=F.Zeros((f,f))
        for i in range(f):
            for j in range(f):
                X_g[i][j]=int(F(x_final[j])**(i+1))
        S_g=F.Zeros((f,1))
        for i in range(f):
            S_g[i][0]=S[i]
        E=np.linalg.inv(X_g)@S_g
        #recovering message
        M=[]
        for i in range(n-k,n):
            if i in r:
                e, = np.where(r==i)
                M.append(int(C[i]-E[e[0]][0]))
            else: M.append(int(C[i]))
        print("An error occured during transmission. Original message : {}".format(M))
        return F(M)

#channel simulation
def channel(F,M,p):
    M_alt=[]
    F_inv=F.elements[1:]
    for i in range(len(M)):
        proba=random.uniform(0,1)
        if proba<p:
            M_alt.append(int(M[i]+random.choice(F_inv)))
        else:
            M_alt.append(int(M[i]))
    return F(M_alt)

#statistics gathering
def statistics(F,samples,rate):
    #creating x and y axis
    P=np.linspace(0,1,samples)
    T=[]
    #randomly creating our message
    M=[]
    for i in range(k):
        M.append(int(random.choice(F.elements)))
    M=F(M)
    #making stats for each proba
    for p in P:
        nb_bits_error=0
        for _ in range(rate):
            C=coding(F,M)
            C_alt=channel(F,C,p)
            D=decoding(F,C_alt)
            w=weight(F,M-D)
            if w !=0 : nb_bits_error+=w
        average=nb_bits_error/rate
        T.append(average/k)
    plt.xscale("log")
    #pyplot graph
    points, = plt.plot(P,T,label="RS(q={};n={},k={},d={})".format(q,n,k,d),linestyle ='none',marker ='o')
    plt.legend(handles = [plt.plot([],ls="-", color=points.get_color())[0]], labels=[points.get_label()])
    #making linear regression
    slope, intercept, r_value, p_value, std_err = stats.linregress(P, T)
    def regrlin(x):
        return slope*x+intercept
    plt.plot(P,regrlin(P),color="red", linestyle=(0, (5, 5)))
    #basic parameters
    plt.ylim(0,1)
    plt.xlabel("Error probability")
    plt.ylabel("Average decoding errors rate")
    plt.grid()
    plt.savefig("RS",dpi=1200)
    plt.show()