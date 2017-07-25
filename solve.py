#function for building the matrix where every line is a clause

import time
import subprocess
import random

def findAnd(c,i):
    if (c[i+1]=='n'or c[i+1]=='N') and (c[i+2]=='d' or c[i+2]=='D'):
        return 1
    else:
        return -1
def findOr(c,i):
    if c[i+1]=='r' or c[i+1]=='R':
        return 1
    else:
        return -1
def findNot(c,i):
    if (c[i+1]=='o'or c[i+1]=='O') and (c[i+2]=='t'or c[i+1]=='T'):
        return 1
    else:
        return -1

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
        #print (operations)  
    return (cnfstring,nVar,nRow+1,inv_variables,variables)
        



#create matrix from the result string
def buildMAtrix(str_results,nvar):
    matrix=[]
    start=time.time()
    splitted_str=str_results.split('\n');
    end=time.time()
    print("time split: "+str(end-start))
    nlines=long(splitted_str[-1])
    start=time.time()
    print("number of solutions: "+str(nlines))
    i=0
    while(i<nlines):     
        matrix.append(map(int,splitted_str[i].split()))#vedere se si riesce a fare meglio dello split
        i+=1
    end=time.time()
    print("time building matrix: "+str(end-start))
    print("elementi matrice: "+ str(nlines*nvar))
    #print(matrix)



def buildFormula(s):
    rs=s[0].split()
    nvar=int(rs[2])
    nclause=int(rs[3])
    #print(nvar)
    res='And('
    for i in range(1,nclause+1):
        temp="Or("
        ri=s[i].split()
        for j in range (0,len(ri)):
            if(int(ri[j])<0):
                temp=temp+'Not(Var'+str(abs(int(ri[j])))+'),'
            elif ri[j]!='0':
                temp=temp+'Var'+ri[j]+','
        temp=temp[0:-1]+'),'
        res=res+temp
        #print (temp)
    res=res[0:-1]+')'
    return res 




f=open("prova","r")
sf=f.readlines()
for i in range(0,7):
    sf.pop(0)
s=buildFormula(sf)


#s='And(Or(Not(var1), var3, var2, var5), Or(Not(var2), var1, var3,var6), Or(var1, var2, var4))'
start3=time.time()
res=()
res = buildDimacsString(s)  
stringadimacs='p cnf '+str(res[1])+' '+str(res[2])+'\n'+res[0]
#print(stringadimacs)
args = ['./bdd_minisat_all',stringadimacs]
#subprocess.call(args)
start2=time.time()
results=subprocess.check_output(args)#getting results from bdd_allsat
end2=time.time()
print("stats:")
print("time allsat: "+str(end2-start2))
start=time.time()
#print(results)
buildMAtrix(results,res[1])
end=time.time()
print("time working on all sat results: "+str(end-start))
print("total time: "+str(end-start3))

#print('\n')
#print(res[1])
#print(res[2])




































 
