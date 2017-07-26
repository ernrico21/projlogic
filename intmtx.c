#include <stdio.h>
#include <stdlib.h>
int * create_matrix(char* nvar,char* s) 
{
	/*printf(s);
	printf("\n");
	printf("%c\n",s[22]);*/
	
	//printf("\n");
	int len= atoi(nvar);
        int *array = (int *)malloc(len * sizeof(int*));
        int j=0;
        for(int i = 0; i < len; i++)
	{ 			
		if(s[j]=='0')	
		{
			array[i]=0;
		}
		else
		{	
			array[i]=1;
		}			              	
		j+=2;
	};
        return array;
}
