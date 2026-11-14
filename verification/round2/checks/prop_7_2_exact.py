#!/usr/bin/env python3
"""Exact coefficient audit of Proposition 7.2(ii). Run: python3 prop_7_2_exact.py"""
import json
from pathlib import Path
from fractions import Fraction
from math import comb, ceil

def plus(a,b):
    r=[0]*max(len(a),len(b))
    for i,v in enumerate(a):r[i]+=v
    for i,v in enumerate(b):r[i]+=v
    return r

def times(a,b,lim=None):
    lim=lim if lim is not None else len(a)+len(b)-2
    r=[0]*(lim+1)
    for i,x in enumerate(a[:lim+1]):
        for j,y in enumerate(b[:lim-i+1]):
            r[i+j]+=x*y
    return r

def power(a,n,lim):
    r=[1]+[0]*lim
    for _ in range(n):r=times(r,a,lim)
    return r

def fpoly(k,lim):
    p1=power([2,3,1],k,lim)
    p2=power([1,3,1],k,lim)
    return plus([0]+p1[:lim],p2[:lim+1])[:lim+1]

def phis(k,r,M,lim):
    f=power(fpoly(k,lim),r,lim)
    return [sum(f[i]*comb(M,s-i)*2**i for i in range(s+1)) for s in range(lim+1)]

def scaled_low_coeffs(k,r,M):
    # Exact normalized coefficients d_(gamma+s) / 2^M:
    # For s<=r-2: [x^s] (x+2)^M f^r / 2^M.
    # At s=r-1 an additional g^r-w^r contribution appears.
    phi=phis(k,r,M,r-1)
    d=[Fraction(phi[s],2**s) for s in range(r)]
    d[-1]+=Fraction((2**k+2*k)**r,1)-Fraction((2*k)**r,2**M)
    return d

def jump_near_low(k,r,M):
    d=scaled_low_coeffs(k,r,M)
    t=r-2
    n=1+r+3*r*k+2*M
    gamma=r*k+M+1
    j=gamma+t
    return (Fraction(1)+(n-j+1)*d[t-1]/d[t]-(n-j)*d[t]/d[t+1])

def main():
    violations=[];bounds=0;theta_checks=0
    for k in range(1,13):
        for r in (3,4,5):
            limit=r
            f=fpoly(k,limit)
            p=power(f,r,limit)
            for i in range(1,r+1):
                a=f[i]
                b=(2**k)*comb(2*k,i-1)+2**i*comb(2*k,i)
                c=(2**k)*(4*k)**i
                if not a<=b<=c:violations.append(('f_bound',k,r,i,a,b,c))
                if p[i] > 2**(r+i)*(4*k)**i*(2**(k*i)):
                    violations.append(('fr_bound',k,r,i,p[i]))
                bounds+=2
            for M in (r, r+1, 6, 8, 15, 20):
                if M<=r-1:continue
                phi=phis(k,r,M,r-1)
                for s in range(1,r):
                    # phis() stores the coefficient *divided by 2^M*.
                    base=Fraction(comb(M,s),2**s)
                    theta=Fraction(phi[s],base)-1
                    q=Fraction(16*k*s*(2**k),M-s)
                    cap=2**r*sum(q**i for i in range(1,s+1))
                    if not 0<=theta<=cap:violations.append(('theta',k,r,M,s,str(theta),str(cap)))
                    for i in range(1,s+1):
                        ratio=Fraction(comb(M,s-i),comb(M,s))
                        if ratio>Fraction(s,M-s)**i:violations.append(('binomial',k,r,M,s,i))
                    theta_checks+=1
    trends={}
    for r in (3,4,5):
        samples=[]
        for k in range(4,15):
            M=2**(k+ceil(Fraction(k,2*r-2)))
            J=jump_near_low(k,r,M)
            samples.append({'k':k,'M':M,'jump':float(J),'target':2*(r-2)+1,
                            'below_limit':J<2*(r-2)+1})
            if not J<2*(r-2)+1:violations.append(('jump_not_below_limit',r,k))
        trends[str(r)]=samples
    output={'coefficient_bound_checks':bounds,'theta_checks':theta_checks,
            'trend':trends,'violations':len(violations),'failure_examples':violations[:20]}
    path=Path(__file__).resolve().parent/'PROP_7_2_EXACT.json'
    with open(path,'w') as f:json.dump(output,f,indent=2)
    print('PROP_7_2_EXACT',bounds,theta_checks,'violations',len(violations))
    for r,a in trends.items():
        print('r',r,'k4',a[0]['jump'],'k14',a[-1]['jump'],'target',a[-1]['target'])
    if violations:print(violations[:4])
    assert not violations

if __name__=='__main__':main()
