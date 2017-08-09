import matplotlib.pyplot as plt
import numpy as np
X = []
Y = []
Y2 = []
X2 = []
f=open('all125','r')
split=f.read().split('\n')
i=1
j=0
while i<len(split)-2:
    #print i
    #j+=1
    nv=float(split[i].split()[3])
    i+=1
    ns=float(split[i].split()[3])
    X.append(ns)
    i+=1
    ta=float(split[i].split()[6])
    Y.append(ta)
    i+=1
    tt=float(split[i].split()[2])
    i+=3
    if tt > 0:
        X2.append(ns*nv)
        Y2.append(tt-ta)
plt.plot(X,Y,'.',label='allsat time')
plt.legend()
plt.show()
plt.plot(X2,Y2,'.',label='Y:time creating matrix X:number of value\'s in matrix')
plt.legend()
plt.show()
