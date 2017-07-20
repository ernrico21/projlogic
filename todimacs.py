#function for building the matrix where every line is a clause
import subprocess

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

def buildDimacsString(c,variables):
    first=1 #if is the first line
    #matrix=[[]]
    cnfstring='';
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
                operations.append('And')   #put the operation in the stack 
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
                    variable += buff.pop(0)
                    k+=1
            if operations[-1] == 'Or':    
                if variable[0]=='-':
                    variable=variable[1:len(variable)]
                    minus=1

                if variable not in variables:
                    variables.update({variable:indexvariable})                    
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
                #matrix[nRow].append(variable) #add the variable of the clause in the row
                cnfstring+=(variable+' ')
                variable=''
            
            elif operations[-1] == 'And':   #means that this clause is finished so i start another one
                #matrix.append([])
                cnfstring+='0\n' 
                nRow+=1
                #variable=""
        elif c[i] == ')':
            if len(buff) != 0:#in theory does not nedd this if
                k=0
                lengbuff=len(buff)
                while k<lengbuff :
                    variable += buff.pop(0)
                    k+=1
            if operations[-1] == 'Not' :
                variable='-'+variable
                operations.pop()
            elif operations[-1] == 'Or' :
                if variable[0]=='-':
                    variable=variable[1:len(variable)]
                    minus=1

                if variable not in variables:
                    variables.update({variable:indexvariable})
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
                #matrix[nRow].append(variable) #add the variable of the clause in the row
                cnfstring+=(variable+' ')
                variable=''
                operations.pop()
            elif operations[-1]== 'And' :
                 cnfstring+='0\n'
        else:
            if c[i]!='('  and j== -1 and c[i]!=' ':
                buff.append(c[i])
        i=i2
        i+=1    
    #matrix.append([nRow+1,len(variables)])
    return (cnfstring,nVar,nRow)
        

s='And(Or(Not(var1), var2, var3), Or(Not(var2), var1, var3), Or(var1, var2, var4))'
variables={}
nVar=0
nClause=0
t=()
t = buildDimacsString(s,variables)  
stringadimacs='p cnf '+str(t[1])+' '+str(t[2])+'\n'+t[0]
print(stringadimacs)
print(variables)
args = ['./bdd_minisat_all',stringadimacs]
subprocess.call(args)






































 
