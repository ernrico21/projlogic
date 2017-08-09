#function for building the matrix where every line is a clause
import ctypes
import time
import subprocess
import sys
import numpy
import os

'''
find if there is the keyword And
'''
def findAnd(c,i):
    if (c[i+1]=='n'or c[i+1]=='N') and (c[i+2]=='d' or c[i+2]=='D'):
        return 1
    else:
        return -1


'''
find if there is the keyword Or
'''
def findOr(c,i):
    if c[i+1]=='r' or c[i+1]=='R':
        return 1
    else:
        return -1


'''
find if there is the keyword Not
'''
def findNot(c,i):
    if (c[i+1]=='o'or c[i+1]=='O') and (c[i+2]=='t'or c[i+1]=='T'):
        return 1
    else:
        return -1


'''
build the dimacs formula from a And(OR(....)) one
'''
def buildDimacsString(c):
    first=1 #if is the first line
    #matrix=[[]]
    cnfstring='';
    variables={}
    inv_variables={}
    nVar=0
    nRow=0 #number of clause
    buff=[]; #for buffering the letter for the variables
    end=0;
    i,i2=0,0 #iterator of the clause
    j=-1 #need to chek if i found a key word
    leng=len(c)
    operations=[] #operation's stack
    variable="";
    indexvariable=1 #index for variables
    minus=0 #ven writing variabile if is negated

    while i<leng:
        j=-1
        i2=i
        if c[i]=='A':
            j=findAnd(c,i)
            if j!=-1 :
                operations.append('And')   #put the operations in the stack 
                i2=i+2              
        elif c[i] == 'O':
            j=findOr(c,i)
            if j!=-1:
                operations.append('Or')
                i2=i+1               
        elif c[i] == 'N':        
            j= findNot(c,i)
            if j!=-1:
                operations.append('Not')
                i2=i+2               
        elif c[i] == ',':                 
            if len(buff) != 0:
                k=0
                lengbuff=len(buff)        
                while k<lengbuff :
                    variable += buff.pop(0)          #when "," means that if i was reading a variable the variable is finished so i pop it off the buff
                    k+=1

            if operations[-1] == 'Or':               #if "or" i just add the variable
                if variable[0]=='-':
                    variable=variable[1:len(variable)]
                    minus=1
                if variable not in variables:                         #if is a new variable i add it in the dictionary
                    variables.update({variable:indexvariable})    
                    inv_variables.update({indexvariable:variable})                
                    variable=str(indexvariable)
                    nVar+=1
                    if minus == 1:
                        variable='-'+variable
                        minus=0
                    indexvariable+=1
                else:
                    variable=str(variables[variable])
		    if minus ==1:                                #if the variable was inside a not i have di put "-" in front of it
                        variable='-'+variable    
                        minus=0                
                cnfstring+=(variable+' ') #add the variable of the clause in the row
                variable=''
            
            elif operations[-1] == 'And':   #"and"means that this clause is finished so i start another one
                cnfstring+='0\n' 
                nRow+=1
        elif c[i] == ')':    #when i see ')' means an operation is finished, so after doing the opesations i pop the operations off the stack
            if len(buff) != 0:     #same as the "," for the variables
                k=0
                lengbuff=len(buff)
                while k<lengbuff :
                    variable += buff.pop(0)
                    k+=1
            if operations[-1] == 'Not' :  #set the controller to 1 for the not
                variable='-'+variable
                operations.pop()
            elif operations[-1] == 'Or' :  
                if variable[0]=='-':
                    variable=variable[1:len(variable)]
                    minus=1

                if variable not in variables:
                    variables.update({variable:indexvariable})
                    inv_variables.update({indexvariable:variable})
                    variable=str(indexvariable)
                    nVar+=1
                    if minus == 1:
                        variable='-'+variable
                        minus=0
                    indexvariable+=1
                else:
                    variable=str(variables[variable])
                if minus ==1:
                    variable='-'+variable    
                    minus=0                    
                cnfstring+=(variable+' ')
                variable=''
                operations.pop()
            elif operations[-1]== 'And' :
                 cnfstring+='0\n'
                 operations.pop()                 
        else:
            if c[i]!='('  and j== -1 and c[i]!=' ':              #put the char in the buff for creating the variable name
                buff.append(c[i])
        i=i2
        i+=1  
    return (cnfstring,nVar,nRow+1,inv_variables,variables)

        
'''
test , tring cut off some variables or some clauses
'''
def buildFormulad(s):
    rs=s[0].split()
    nvar=int(rs[2])
    nclause=int(rs[3])
    res='And('
    i=1
    k=1
    #k=nclause/10
    n=0;
    while k< (nclause+1):
        n=0
        ri=s[i].split()
        if ri[0]!='0':
            temp="Or("
            for j in range (0,len(ri)):
                if(int(ri[j])<0):
                    inte=int(ri[j])
                    if inte%2==0:
                        temp=temp+'Not(Var'+str(abs(inte))+'),'
                        n+=1
                elif ri[j]!='0':
                    inte=int(ri[j])
                    if inte%2==0:
                        temp=temp+'Var'+str(inte)+','
                        n+=1
            temp=temp[0:-1]+'),'
            if n==0:
                temp=temp[0:-4]                
            res=res+temp
            k+=1
        i+=1
    res=res[0:-1]+')'
    return res 



'''
metod for getting the And(Or(..)) formula from a dimacs
'''
def buildFormula(s):
    rs=s[0].split()
    nvar=int(rs[2])
    nclause=int(rs[3])
    res='And('
    i=1
    k=1
    while k< (nclause+1):
        ri=s[i].split()
        if ri[0]!='0':
            temp="Or("
            for j in range (0,len(ri)):
                if(int(ri[j])<0):
                    temp=temp+'Not(Var'+str(abs(int(ri[j])))+'),'
                elif ri[j]!='0':
                    temp=temp+'Var'+ri[j]+','
            temp=temp[0:-1]+'),'
            res=res+temp
            k+=1
        i+=1
    res=res[0:-1]+')'
    return res



'''
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
return the result matrix and the dictionary that give the index if a variable
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
'''
def getSolutions(s,stat=0,smatrix=0,name="inputfile"):

    start=time.time()
    res=()
    res = buildDimacsString(s)  
    stringadimacs='p cnf '+str(res[1])+' '+str(res[2])+'\n'+res[0]
    f=open("in","w")
    f.write(stringadimacs)
    f.close()
    args = ['./bdd_minisat_all',"in",'-n 100000000']
    
    startnormal=time.time()

####getting results from bdd_allsat

    p=subprocess.call(args)
    endallsatnormal=time.time()
    print("time allsat to find the solutions: "+str(endallsatnormal-startnormal)+"\n")
    fout=open("out","r")  

####using the c library
    lib_cpp = ctypes.CDLL('./intmtx.so')
    lib_cpp.create_matrix.restype = ctypes.POINTER(ctypes.c_int * res[1])

    startmatrixc=time.time()
    #print startmatrixc
####read the file row by ow and append 0 and 1 to the matrix
    matrix=[]
    i=0
    line=fout.readline()
    timein1=time.time()
    while line:
        j=0
        matrix.append([])
        while j < 2*(res[1]):
            if line[j]=='0':	
                matrix[i].append(0)
            elif line [j]=='1':
                matrix[i].append(1)            
            j+=2
        i+=1 
        line=fout.readline()
    nlines=i
    end=time.time()
    fout.close()
    
    if smatrix==1:
        print(numpy.matrix(matrix))
    if stat==1:
        f2=open("res",'a')
        f2.write("number of variables: "+str(res[1])+"\n")
        f2.write("number of solutions: "+str(nlines)+"\n")
        #print("matrix elements: "+ str(nlines*res[1]))
        f2.write("time allsat to find the solutions: "+str(endallsatnormal-startnormal)+"\n")
        #print("time building matrix: "+str(end-startmatrixc))
        #print("time spend converting in c: "+ str(tottime))
        f2.write("total time: "+str(end-startnormal)+"\n\n")    
        f2.close()
    elif stat ==2:
        print("number of variables: "+str(res[1])+"\n")
        print("number of solutions: "+str(nlines)+"\n")
        #print("matrix elements: "+ str(nlines*res[1]))
        print("time allsat to find the solutions: "+str(endallsatnormal-startnormal)+"\n")
        #print("time building matrix: "+str(end-startmatrixc))
        #print("time spend converting in c: "+ str(tottime))
        print("total time: "+str(end-startnormal)+"\n\n")  
    elif stat==3:
        f3=open("all150",'a')
        f3.write(name+"\n")
        f3.write("number of variables: "+str(res[1])+"\n")
        f3.write("number of solutions: "+str(nlines)+"\n")
        #print("matrix elements: "+ str(nlines*res[1]))
        f3.write("time allsat to find the solutions: "+str(endallsatnormal-startnormal)+"\n")
        #print("time building matrix: "+str(end-startmatrixc))
        #print("time spend converting in c: "+ str(tottime))
        f3.write("total time: "+str(end-startnormal)+"\n\n")    
        f3.close()
        del matrix
        del res
    #return (matrix,res[3]) 
    
'''

f=open("prova","r")
sf=f.readlines()
i=0
while i>=0:
    if sf[0][0]=='c':
        sf.pop(0)
        i+=1
    else:
        i=-1

s=buildFormula(sf)
#print s
#print(buildDimacsString(s)[0])
getSolutions(s,2,0,'')
'''

#print(s)
#s='And(Or(Not(var1), var3, var2, var5), Or(Not(var2), var1, var3,var5), Or(var1, var2, var4))'




k=57
j=k
while j<k+1:
    name="uf150-0"+str(j)+".cnf"
    f=open(os.path.join("cnf150",name))
    print name
    print 'number of variables: 150'
    sf=f.readlines()
    i=0
    while i>=0:
        if sf[0][0]=='c':
            sf.pop(0)
            i+=1
        else:
            i=-1
    s=buildFormula(sf)
    del sf
    getSolutions(s,3,0,name)
    del s
    j+=1














 
