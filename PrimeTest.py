'''
Created on 2012-12-12

@author: chenkuantong

www.chenkuantong.com
'''
from itertools import *
from math import *
import operator

def native_prime_test1(n):
    return all(imap(lambda x:n%x!=0, range(2,n)))

def native_prime_test2(n):
    return all(imap(lambda x:n%x!=0, range(2,n/2)))

def native_prime_test3(n):
    return all(imap(lambda x:n%x!=0, range(2, int(floor(sqrt(n))))))

def wowrange(start, stop, step=1):
    if step == 0:
        raise ValueError('step must be != 0')
    elif step < 0:
        proceed = operator.gt
    else:
        proceed = operator.lt
    while proceed(start, stop):
        yield start
        start += step
    
def native_prime_test4(n):
    return all(imap(lambda x:n%(2*x+1)!=0, wowrange(1, long(sqrt(n))/2 ) ))& (n%2 !=0)

def native_prime_test5(n,prime_seed):
    c=reduce(lambda x,y:x*y, prime_seed,1)
    i=filter(lambda x:all(map(lambda y: x%y!=0, prime_seed)), range(1,c))
    m=map(lambda (x,y): x*c+y, product(range(0,int(ceil(sqrt(n)/c))),i))
    return all(imap(lambda x:n%x!=0, prime_seed))&all(imap(lambda x:n%x!=0, m))

def fermat_probabilistic_test(n,a):
    return reduce(lambda x,y: a*x%n, range(1,n), 1)==1

def mypower(a,d,n):
    log2d=int(log(d,2))+1
    base=a
    B=[]
    for k in range(log2d):
        B.append(base)
        base=(base*base)%n
    mask_base=[0]*log2d
    tn=d
    for k in range(log2d):
        if tn%2==1:
            tn=(tn-1)/2
            mask_base[k]=1
        else:
            tn=tn/2
    FPL=filter(lambda x:x[0]==1,zip(mask_base,B))
    return reduce(lambda P1,P2:(P1*P2[1])%n, FPL, 1)

def miller_rabin_probabilistic_test(n,a):
    s=list(takewhile(lambda x: ((n-1)%(2**x))==0, range(1, int(log(n,2))+1)))[-1]
    d=(n-1)/(2**s)
    ad=mypower(a,d,n)
    if ad==1:
        return True
    for k in range(s):
        if ad==n-1:
            return True
        ad=(ad*ad)%n
    return False
def gcd(n,m):
    if m>n:
        return gcd(m,n)
    if m==0:
        return n
    if m==1:
        return 1
    return gcd(m,n%m)
def jacobi_quadratic_residue(n,m):
    if n%2==0:
        raise "Input n should be odd number"
    if m==1:
        return 1
    if m==0:
        return 0
    if m==2:
        return (-1)**((n-1)*(n+1)/8)
    if m==n-1:
        return (-1)**((n-1)/2)
    if m%2==0:
        return jacobi_quadratic_residue(n,m/2)*jacobi_quadratic_residue(n,2)
    if (m>n):
        return jacobi_quadratic_residue(n,m%n)
    if (n>m):
        return jacobi_quadratic_residue(m,n)*(-1)**((m-1)*(n-1)/4)
    
def solovay_strassen_probabilistic_test(n,a):
    if n%2==0:
        raise "p should be odd number"
    return (-1)**((n-1)/2)==jacobi_quadratic_residue(n,a)

def is_pure_power(n):
    d=int(log(n,2))
    f=filter(lambda x: long(x[0])**x[1]==n, map(lambda x: (n**(1/float(x)),x), range(2, d+1)))
    return len(f)!=0

def find_smallest_r(n):
    logn2=floor(log(n,2))**2
    for r in wowrange(2,(long(sqrt(n))+1)):
        powk=n%r
        if powk==0:
            return -1   #this is a composite
        found_flag=True
        for k in range(0, int(logn2)):
            if powk==1:#or(n)<logn2
                found_flag=False
                break
            powk=(powk*n)%r
        if found_flag:
            return r
    return -2           #this is a prime

def poly_quard(P,n,r):
    M=map(lambda (x,y): ((x[0]+y[0])%r,(x[1]*y[1])%n), product(zip(range(r),P),repeat=2))
    P=[0]*r
    for (k,a) in M:
        P[k]+=a
    P=map(lambda x:x%n,P)
    return P

def poly_mul(P1,P2,n,r):
    M=map(lambda (x,y): ((x[0]+y[0])%r,(x[1]*y[1])%n), product(zip(range(r),P1),zip(range(r),P2)))
    P=[0]*r
    for (k,a) in M:
        P[k]+=a
    P=map(lambda x:x%n,P)
    return P

def poly_power(a,n,r):
    #(X+a)^n (mod n, X^r-1)
    #11 --> 1011
    logn=int(log(n,2))+1
    poly_base=[0]*logn
    P0=[0]*r
    PU=[0]*r
    PU[0]=1
    P0[0],P0[1]=a,1
    
    for k in range(logn):
        poly_base[k]=P0
        P0=poly_quard(P0,n,r)
    mask_base=[0]*logn
    tn=n
    for k in range(logn):
        if tn%2==1:
            tn=(tn-1)/2
            mask_base[k]=1
        else:
            tn=tn/2
    FPL=filter(lambda x:x[0]==1,zip(mask_base,poly_base))
    return reduce(lambda P1,P2:poly_mul(P1,P2[1],n,r), FPL, PU)

def AKS_prime_test(n):
    if is_pure_power(n):
        return False
    r=find_smallest_r(n) 
    if r==-1:
        return False
    elif r==-2:
        return True
    for a in range(1, int(sqrt(r)*log(n,2)+1)):
        P=poly_power(a,n,r)
        P[0] -= a
        P[-1] -= 1
        if not all(map(lambda x:x==0, P)):
            return False
    return True
           
from random import randint

if __name__=='__main__':
    n=reduce(lambda x,y: x*y[1], filter(lambda x:x[0], (map(lambda y:(AKS_prime_test(y),y), range(5,100)))), 1)*3*947+2
    print 'n=', n
    MR=map(lambda a: miller_rabin_probabilistic_test(n,a), range(2,100))
    print 'miller rabin test gives ',all(MR)
    print native_prime_test4(n)
    print AKS_prime_test(n)
    #MR=map(lambda a: miller_rabin_probabilistic_test(n,a), range(2,100))
