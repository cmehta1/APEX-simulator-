#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<limits.h>

#include "simulator.h"


int pc_exe_int;
int pc_exe_mul;
int pc_exe_mem1;


int cycles_completed=0;
int update_pc;
int current_pc=0;

//no. of instructions read and stored in array
int instru_count=0;

//starting index of instructions
int offset=20000;

//registers
int R[8];
int X;
int v_memory[10000];

//register status bit
int reg_status[9];

//physical registers
int phy_R[16];
int phy_R_status[16];

//REGISTER RENAMING
//free list
int l_free[16];
int alloc[16];
int renamed[16];
int rename_table[9];

//instruction array
char instruction[instructs][20];

//flags
int zero_f;
int halt_f;
int completion_f; //instructions finished
int dependency_check;
int dependent_reg;
//flag for IQ space check
int IQfull_f;
int LSQfull_f;
//flag for free list
int free_l_f;
int rob_f;
int mul_occ_f;

int predict_taken;
int drf_branch;

//flags for INT and MUL stall
int install_f;
int mulstall_f;

//program counters for each stage
int commit_p,wb_p,mem3_p,mem2_p,mem_p,mul4_p,mul3_p,mul2_p,mul1_p,int_p,exe_p,decode2_p,decode1_p,fetch2_p,fetch1_p;


void pc_reset(){
	int commit_p=-1;
	int wb_p=-1;
	int mem3_p=-1;
	int mem2_p=-1;
	int mem_p=-1;
	int mul4_p=-1;
	int mul3_p=-1;
	int mul2_p=-1;
	int mul1_p=-1;
	int int_p=-1;
	int exe_p=-1;
	int decode2_p=-1;
	int decode1_p=-1;
	int fetch2_p=-1;
	int fetch1_p=-1;
}

void flag_set_0(){
	
	zero_f=0;
	halt_f=0;
	completion_f=0;
	IQfull_f=0;
	LSQfull_f=0;
	free_l_f=0;
	rob_f=0;

    install_f=0;
    mulstall_f=0;
    mul_occ_f=0;
	
	predict_taken=0;
    drf_branch=0;
}

void execute_pc_set(){
	pc_exe_int=-1;
    pc_exe_mul=-1;
    pc_exe_mem1=-1;
}
//instructions types

//instruction in each stage
struct instru_info *fetch1_instru,*fetch2_instru,
                    *decode1_instru,*decode2_instru,
                    *execute_instru,
                    *IQ[8],*IQhead_INT_instru,*IQhead_MUL_instru,
                    *LSQ[4],*LSQhead_instru,
					*ROB[16],
					*int_instru,
                    *mul1_instru,*mul2_instru,*mul3_instru,*mul4_instru,
                    *memory1_instru,*memory2_instru,*memory3_instru,
                    *wb_instru,
                    *commit_instru;
					
void info_ptr_set(){
	decode1_instru=NULL;
	decode2_instru=NULL;
	execute_instru=NULL;

	IQhead_INT_instru=NULL;
	IQhead_MUL_instru=NULL;
	LSQhead_instru=NULL;

    int_instru=NULL;

    mul1_instru=NULL;
    mul2_instru=NULL;
    mul3_instru=NULL;
    mul4_instru=NULL;

    memory1_instru=NULL;
    memory2_instru=NULL;
    memory3_instru=NULL;

	wb_instru=NULL;
	fetch2_instru=NULL;
	fetch1_instru=NULL;
}

//roll back if branch
void rollbacking(){

    //printf("\nRollback called.\n");
    int i_ROB=0,phy_r_temp=-1,i, i_IQ=0, i_LSQ=0;

    //printf("\nRollback before ROB.\n");

    for(i_ROB=0;i_ROB<16;i_ROB++)
    {
        if(ROB[i_ROB]==int_instru)
            break;
    }
    //except branch itself
    i_ROB++;
    //printf("\nRollback:branch at:%d.\n",i_ROB);
    for(;i_ROB<16;i_ROB++)
    {
        //printf("\nRollback:check for rob entry.\n");
        if(ROB[i_ROB]==NULL)
        {
           // printf("\nRoll back: checkpoint.\n");
            break;
        }
        /*
        alloc clear
        free list
        rename table clear
        phy_R_status clear
        */
        if(ROB[i_ROB]->op_code<9)
        {
           // printf("\nRollback:reseting renaming structures.\n");
            phy_r_temp=ROB[i_ROB]->arg1_addr;
            phy_R_status[phy_r_temp]=0;
            alloc[phy_r_temp]=0;
            rename_table[ROB[i_ROB]->arf_addr]=-1;
            for(i=0;i<16;i++)
            {
                if(l_free[i]==-1)
                {
                    l_free[i]=phy_r_temp;
                    break;
                }
            }
        }

        //printf("\nRollback:clear IQ.\n");
        for(i_IQ=0;i_IQ<8;i_IQ++)
        {
            if(IQ[i_IQ]==ROB[i_ROB])
            {
                IQ[i_IQ]=NULL;
            }
        }

        //printf("\nRollback:clear LSQ.\n");
        for(i_LSQ=0;i_LSQ<4;i_LSQ++)
        {
            if(LSQ[i_LSQ]==ROB[i_ROB])
            {
                LSQ[i_LSQ]=NULL;
            }
        }

        //printf("\nRollback:Set NULL.\n");
        if(wb_instru==ROB[i_ROB])
            wb_instru=NULL;

        if(memory1_instru==ROB[i_ROB])
            memory1_instru=NULL;

        if(memory2_instru==ROB[i_ROB])
            memory2_instru=NULL;

        if(memory3_instru==ROB[i_ROB])
            memory3_instru=NULL;


        if(mul1_instru==ROB[i_ROB])
            mul1_instru=NULL;


        if(mul2_instru==ROB[i_ROB])
            mul2_instru=NULL;


        if(mul3_instru==ROB[i_ROB])
            mul3_instru=NULL;


        if(mul4_instru==ROB[i_ROB])
            mul4_instru=NULL;

        ROB[i_ROB]=NULL;
    }

    //printf("\nRollback: ROB checking complete.\n");
    if(decode1_instru!=NULL && decode1_instru->op_code<9)
    {
        //printf("\nRollback:reseting renaming structures for decode 1.\n");
        phy_r_temp=decode1_instru->arg1_addr;
        phy_R_status[phy_r_temp]=0;
        alloc[phy_r_temp]=0;
        rename_table[decode1_instru->arf_addr]=-1;
        for(i=0;i<16;i++)
        {
            if(l_free[i]==-1)
            {
                l_free[i]=phy_r_temp;
                break;
            }
        }
    }
    decode1_instru=NULL;

    if(decode2_instru!=NULL && decode2_instru->op_code<9)
    {
        //printf("\nRollback:reseting renaming structures for decode 2.\n");
        phy_r_temp=decode2_instru->arg1_addr;
        phy_R_status[phy_r_temp]=0;
        alloc[phy_r_temp]=0;
        rename_table[decode2_instru->arf_addr]=-1;
        for(i=0;i<16;i++)
        {
            if(l_free[i]==-1)
            {
                l_free[i]=phy_r_temp;
                break;
            }
        }
    }
    decode1_instru=NULL;
    fetch1_instru=NULL;
    fetch2_instru=NULL;

    //printf("\nRollback done complete.\n");
    //done rolling back
}

//free pointers at exit
void quit(){
	
	free(fetch1_instru);
	free(fetch2_instru);
	free(decode1_instru);
	free(decode2_instru);
	free(execute_instru);

	free(IQhead_INT_instru);
	free(IQhead_MUL_instru);

    free(LSQhead_instru);

    free(int_instru);


    free(mul1_instru);
    free(mul2_instru);
    free(mul3_instru);
    free(mul4_instru);

    free(memory1_instru);
    free(memory2_instru);
    free(memory3_instru);

	free(wb_instru);
	
	info_ptr_set();
	
	free(commit_instru);
	commit_instru=NULL;

	//free IQ pointers
	int i=0,j=0,k=0;
	while(i<8)
    {
        free(IQ[i]);
		i++;
    }
	memset(IQ, NULL, 8 * sizeof(IQ[0]));
	
	//free LSQ pointers
	while(j<4)
    {
        free(LSQ[j]);
		j++;
    }
	memset(LSQ, NULL, 4 * sizeof(LSQ[0]));
	
	//free ROB pointers
    while(k<16)
    {
        free(ROB[k]);
        k++;
    }
	memset(ROB, NULL, 16 * sizeof(ROB[0]));
}

//functions for each instruction operation

void operation_bz(int lit){
	update_pc=int_instru->pc+lit-20000;
}

void operation_bnz(int lit){
	update_pc=int_instru->pc+lit-20000;
}

void operation_jump(int reg,int lit){
	update_pc=(reg+lit-20000);
}

void operation_bal(int reg,int lit){
	update_pc=(reg+lit-20000);
	phy_R[int_instru->arg1_addr]=int_instru->arg1;
}

//func to extract inst opcode & args in D/RF 1
int inst_components(){
        int d1_pc=decode1_instru->pc-20000;

        printf("\nPC decode stage 1: %d Instruction: %s",d1_pc,instruction[d1_pc]);

        //get instruction op code
        char *token,temp_inst[20];
        strcpy(temp_inst,instruction[d1_pc]);
        token=strtok(temp_inst," ,\n");
        int i=0;
        for(i=0;i<15;i++)        {
            if(strcmp(token, operate[i])==0)
                break;
        }
        decode1_instru->op_code=i;

        //destination register
        if(i<10)
        {
            token=strtok(NULL," ,\n");

            if(token==NULL)
            {
                decode1_instru->arg1_addr=-1;
                decode1_instru->arg1=0;
                decode1_instru->arg1_valid_bit=0;
            }
            else if(token[0]=='R')
            {
                decode1_instru->arg1_addr=token[1]-'0';
                decode1_instru->arg1=R[decode1_instru->arg1_addr];
            }
            else if(token[0]=='X')
            {
                decode1_instru->arg1=X;
                decode1_instru->arg1_addr=8;
            }
            else
            {
                decode1_instru->arg1_addr=-1;
                decode1_instru->arg1=atoi(token);
                decode1_instru->arg1_valid_bit=0;
            }
        }
        else
        {
            decode1_instru->arg1_addr=-1;
            decode1_instru->arg1=0;
            decode1_instru->arg1_valid_bit=0;

        }

        //to update R[] in write back save address
        decode1_instru->arf_addr=decode1_instru->arg1_addr;

        //read argument 2
        token=strtok(NULL," ,\n");

        if(token==NULL)
        {
            decode1_instru->arg2_addr=-1;
            decode1_instru->arg2=0;
            decode1_instru->arg2_valid_bit=0;
        }
        else if(token[0]=='R')
        {
            decode1_instru->arg2_addr=token[1]-'0';
            decode1_instru->arg2=R[decode1_instru->arg2_addr];
        }
        else if(token[0]=='X')
        {
            decode1_instru->arg2=X;
            decode1_instru->arg2_addr=8;
        }
        else
        {
            decode1_instru->arg2_addr=-1;
            decode1_instru->arg2=atoi(token);
            decode1_instru->arg2_valid_bit=0;
        }

        //read argument 3
        token=strtok(NULL," \n");

        if(token==NULL)
        {
            decode1_instru->arg3_addr=-1;
            decode1_instru->arg3=0;
            decode1_instru->arg3_valid_bit=0;
        }
        else if(token[0]=='R')
        {
            decode1_instru->arg3_addr=token[1]-'0';
            decode1_instru->arg3=R[decode1_instru->arg3_addr];
        }
        else if(token[0]=='X')
        {
            decode1_instru->arg3=X;
            decode1_instru->arg3_addr=8;
        }
        else
        {
            decode1_instru->arg3_addr=-1;
            decode1_instru->arg3=atoi(token);
            decode1_instru->arg3_valid_bit=0;
        }
        if(decode1_instru->op_code==13)
        {
            decode1_instru->arg1_addr=8;
            decode1_instru->arf_addr=8;

            if(fetch1_instru!=NULL)
                decode1_instru->arg1=fetch1_instru->pc;
        }

    return d1_pc;
}

//initialize menu choice
void initialize(){
	int i=0;

	instru_count=0;

	//initializing flags
	flag_set_0();

	dependency_check = 0;
	dependent_reg = -1;

	execute_pc_set();

	//initializing program counters
	update_pc=INT_MAX;
	current_pc = 0;

    //total cycles done
    cycles_completed=0;

    //initializing registers
	memset(R, 0, 8 * sizeof(R[0]));

	X=0;
	
	memset(reg_status, 0, 9 * sizeof(reg_status[0]));
	memset(rename_table, -1, 9 * sizeof(rename_table[0]));
	
	//physical registers
    // 0 - valid
	memset(phy_R, 0, 16 * sizeof(phy_R[0]));
	memset(phy_R_status, 0, 16 * sizeof(phy_R_status[0])); //invalid status
	
	//renaming initializing
	memset(alloc, 0, 16 * sizeof(alloc[0])); //not allocated
	memset(renamed, 0, 16 * sizeof(renamed[0])); //not renamed
	
	memset(ROB, NULL, 16 * sizeof(ROB[0]));
	
	
    i=0;
     while(i<16){
        //renaming initializing
        l_free[i]=i;
		i++;
    }

	//initializing memory
	memset(v_memory, 0, 10000 * sizeof(v_memory[0]));

	//initializing IQ array
	memset(IQ, NULL, 8 * sizeof(IQ[0]));

    //initializing LSQ array
	memset(LSQ, NULL, 4 * sizeof(LSQ[0]));

    //open file to read
	FILE *fptr=fopen("Input 1.txt","r");

	//check if able to open file
	if(fptr==NULL)
	{
		printf("\nFile not found.\n");
		exit(-1);
	}

	char temp[20];

	while(!feof(fptr))
	{
		while(fgets(temp,20,fptr)!=NULL)
		{
			strcpy(instruction[instru_count++],temp);
			printf("%s",instruction[instru_count-1]);
		}
	}
	printf("\n\nNumber of instructions read: %d\n\n",instru_count);

	info_ptr_set();
	offset=20000;

    //reset program counters
   pc_reset();

	return;
}

//FETCH stage 1
int first_fetch(){

    //halt
    if(halt_f==1)
    {
        printf("\nHalt encountered fetch 2 stage.\n\n");
        fetch1_instru=NULL;
        return -1;
    }

    //printf("fetch stage 1 before dependent flag 1 check.\n");
    if(dependency_check==1)
    {
        printf("\nSTALL in fetch stage 1\n\n");
		//return fetch1_instru->pc-20000;
        return -1;
    }

    //printf("fetch stage 1 after dependent flag 1 check.\n");
    if(IQfull_f==1)
    {
        printf("STALL in fetch 1 due to IQ full.\n");
        return -1;
    }

    if(rob_f==1)
    {
        printf("STALL in fetch 1 due to ROB full.\n");
        return -1;
    }

    //printf("fetch stage 1 before flag freelist 1 check.\n");

    if(free_l_f==1)
    {
        printf("STALL in fetch 1 due to no free physical reg in free list.\n");
        return -1;
    }

    //printf("fetch stage 1 after flag freelist 1 check.\n");

    //branching
    if(update_pc!=INT_MAX)
    {
        //printf("\nPC fetch stage 1: %d Instruction: %s\n",current_pc,instruction[current_pc]);
        fetch1_instru=(struct instru_info*)malloc(sizeof(struct instru_info));
        if((int_instru->op_code==10) || (int_instru->op_code==11))
        {
            current_pc=update_pc;    // bcoz out of order execution
        }
        else if ((int_instru->op_code==12) || (int_instru->op_code==13))
        {
            current_pc=update_pc;
        }
		if (drf_branch==1 &&(decode1_instru->op_code==10 || decode1_instru->op_code==11))
        {
            current_pc=update_pc;
            drf_branch=0;
        }
        fetch1_instru->pc=current_pc+20000;
        update_pc=INT_MAX;
        fetch1_instru=NULL;

        if(current_pc==instru_count)
        {
            completion_f=1;
        }
        return -1;
    }

    //printf("fetch stage 1 current_pc>=instru_count check.\n");

	if(predict_taken==1)
    {
        printf("\nSTALL in fetch stage 1 due to branch prediction of taken.\n");
        return -1;
    }
    //no more instructions to fetch
    if(current_pc>=instru_count)
    {
        printf("\nNo instructions to fetch in stage 1.\n");
        fetch1_instru = NULL;
        return -1;
    }

    //printf("fetch stage 1 dependency_check 0 check\n");
    //get next instruction
    if(dependency_check==0)
    {
        //printf("\nPC fetch stage 1: %d Instruction: %s\n",current_pc,instruction[current_pc]);
        fetch1_instru=(struct instru_info*)malloc(sizeof(struct instru_info));
        fetch1_instru->pc=current_pc+20000;
        current_pc++;
        if((current_pc-1)==instru_count)
        {
            completion_f=1;
        }
        return fetch1_instru->pc-20000;
    }

    //printf("fetch stage 1 last.\n");
}

//FETCH stage 2
int second_fetch(){

    //halt
    if(halt_f==1)
    {
        printf("\nHalt encountered fetch 2 stage.\n\n");
        fetch2_instru=NULL;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("\nSTALL due to branch fetch 2 stage.\n\n");
        fetch2_instru=NULL;
        return -1;
    }
	if(predict_taken==1)
    {
        printf("\nSTALL due to branch prediction of taken.\n");
        fetch2_instru=NULL;
        return -1;
    }
    //stall
    if(dependency_check==1)
    {
        printf("\nSTALL in fetch 2 stage.\n\n");
        return -1;
        //return fetch2_instru->pc-20000;
    }

    if(IQfull_f==1)
    {
        printf("STALL in fetch 2 due to IQ full.\n");
        return -1;
    }

    if(rob_f==1)
    {
        printf("STALL in fetch 2 due to ROB full.\n");
        return -1;
    }

    if(free_l_f==1)
    {
        printf("STALL in fetch 2 due to no free physical reg in free list.\n");
        return -1;
    }
    //No instructions to get from fetch 1 stage
    if(fetch1_instru==NULL)
    {
        printf("\nNo instructions in fetch 2 stage.\n\n");
        fetch2_instru=NULL;
        return -1;
    }

    //get next intruction from fetch stage 1 to 2
    if(dependency_check==0)
    {
        fetch2_instru=fetch1_instru;
        int fetch2_pc=fetch2_instru->pc-20000;
        //printf("\nPC fetch stage 2: %d  Instruction: %s\n",fetch2_pc,instruction[fetch2_pc]);
        return fetch2_pc;
    }
}

//D/RF 1
int first_decode(){
    //halt
    if(halt_f==1)
    {
        printf("\nHalt encountered fetch 2 stage.\n\n");
        decode1_instru=NULL;
        return -1;
    }
    //in case of branch
    if(update_pc!=INT_MAX)
    {
        printf("\nSTALL due to branch decode stage 1.\n\n");
        decode1_instru=NULL;
        return -1;
    }

    //in case of stall in case of dependency
    if(dependency_check==1)
    {
        printf("\nSTALL in decode stage 1\n\n");
        return -1;
        //return decode1_instru->pc-20000;
    }

    // no instruction to get from fetch 2
    if(fetch2_instru==NULL)
    {
        printf("\nNo instructions to decode stage 1.\n\n");
        decode1_instru=NULL;
        return -1;
    }

    //process next incoming instruction
    if(dependency_check==0)
    {
        decode1_instru=fetch2_instru;
        int decode1_pc = -1;
        int i_IQ,i_ROB,i_LSQ;

        for(i_ROB=0;i_ROB<16;i_ROB++)
        {
            if(ROB[i_ROB]==NULL)
                break;
        }
        if(i_ROB==16)
        {
            rob_f=1;
            printf("\nSTALL in Decode stage 1 due to ROB full.\n");
            return -1;
        }
        else
        {
            rob_f=0;

            //call to func to extract opcode & args from inst
            decode1_pc=inst_components();

            if(decode1_instru->op_code<8 ||decode1_instru->op_code>9)
            {

                for(i_IQ=0;i_IQ<8;i_IQ++)
                {
                    if (IQ[i_IQ]==NULL)
                        break;
                }

                if(i_IQ==8)
                {
                    //STALL instructions due to IQ full
                    IQfull_f=1;
                    printf("\nSTALL in Decode stage 1 due to IQ full.\n");
                    return -1;
                }
            }
            IQfull_f=0;

            if(decode1_instru->op_code==8 ||decode1_instru->op_code==9)
            {
                for(i_LSQ=0;i_LSQ<4;i_LSQ++)
                {
                    if (LSQ[i_LSQ]==NULL)
                        break;
                }

                if(i_LSQ==8)
                {
                    //STALL instructions due to IQ full
                    LSQfull_f=1;
                    printf("\nSTALL in Decode stage 1 due to LSQ full.\n");
                    return -1;
                }
            }
            LSQfull_f=0;

        }
        if(decode1_instru->op_code==10 || decode1_instru->op_code==11)
        {
            decode1_instru->arg1_addr=decode2_instru->arg1_addr;
        }
		if(decode1_instru->arg2<0)
            {
                predict_taken=1;
                drf_branch=1;
                update_pc=decode1_instru->pc+decode1_instru->arg2-20000;
            }
        //printf("   Decode:  %d:%d:%d:%d:%d:%d:%d:%d\n\n",decode1_instru->op_code,decode1_instru->arg1,decode1_instru->arg1_addr,decode1_instru->arg2,decode1_instru->arg2_addr,decode1_instru->arg3,decode1_instru->arg3_addr,decode1_instru->pc);

        if(decode1_instru->op_code==14)
        {
            halt_f=1;
        }
        return decode1_pc;
    }


}

//D/RF 2
int second_decode(){
	predict_taken=0;
    if(update_pc!=INT_MAX)
    {
        printf("\nSTALL due to branch decode stage 2.\n\n");
        decode2_instru=NULL;
        return -1;
    }

    if(dependency_check==1)
    {
        printf("\nSTALL in decode stage 2\n\n");
        /*  to copy latest value of dependent register from write back so that updated
        value is passed to execute in next cycle when dependency is removed via commit stage. */
        if(decode2_instru->op_code==9)
        {
            if(decode2_instru->arg1_addr==dependent_reg && decode2_instru->arg1_valid_bit==1)
            {
                decode2_instru->arg1=phy_R[decode2_instru->arg1_addr];
                decode2_instru->arg1_valid_bit=phy_R_status[decode2_instru->arg1_addr];
            }
        }

        //BZ / BNZ internal reg for introducing dependency
        if(decode2_instru->op_code==10 ||decode2_instru->op_code==11)
        {
            if(decode2_instru->arg1_addr==dependent_reg && decode2_instru->arg1_valid_bit==1)
            {
                decode2_instru->arg1=phy_R[decode2_instru->arg1_addr];
                decode2_instru->arg1_valid_bit=phy_R_status[decode2_instru->arg1_addr];
            }
        }

        if(decode2_instru->arg2_addr==dependent_reg && decode2_instru->arg2_valid_bit==1)
        {
            decode2_instru->arg2=phy_R[decode2_instru->arg2_addr];
            decode2_instru->arg2_valid_bit=phy_R_status[decode2_instru->arg2_addr];
        }
        if(decode2_instru->arg3_addr==dependent_reg && decode2_instru->arg3_valid_bit==1)
        {
            decode2_instru->arg3=phy_R[decode2_instru->arg3_addr];
            decode2_instru->arg3_valid_bit=phy_R_status[decode2_instru->arg3_addr];

        }
        return -1;
    }

    if(decode1_instru==NULL)
    {
        printf("\nNo instructions to decode in stage 2.\n\n");
        decode2_instru=NULL;
        return -1;
    }



    if(dependency_check==0)
    {
        decode2_instru=decode1_instru;
        int decode2_pc=decode2_instru->pc-20000;

        //printf("\nPC decode stage 2: %d Instruction: %s",decode2_pc,instruction[decode2_pc]);

        //for source registers
        //arg1 for STORE
        if(decode2_instru->op_code==9)
        {
            if(decode2_instru->arg1_addr!=-1)
            {
                if(rename_table[decode2_instru->arg1_addr]!=-1)
                {
                    decode2_instru->arg1_addr=rename_table[decode2_instru->arg1_addr];
                    decode2_instru->arg1=phy_R[decode2_instru->arg1_addr];
                    decode2_instru->arg1_valid_bit=phy_R_status[decode2_instru->arg1_addr];
                }
                else
                
				{
					decode2_instru->arg1=R[decode2_instru->arg1_addr];
                    decode2_instru->arg1_addr=-1;
                    decode2_instru->arg1_valid_bit=0;
                }
            }
        }

        if(decode2_instru->arg2_addr!=-1)  //not lit & exists
        {
            if(rename_table[decode2_instru->arg2_addr]!=-1)
            {
                decode2_instru->arg2_addr=rename_table[decode2_instru->arg2_addr];
                decode2_instru->arg2=phy_R[decode2_instru->arg2_addr];
                decode2_instru->arg2_valid_bit=phy_R_status[decode2_instru->arg2_addr];

            }
                else
                {
					decode2_instru->arg2=R[decode2_instru->arg2_addr];
                    decode2_instru->arg2_addr=-1;
                    decode2_instru->arg2_valid_bit=0;
                }
        }

        if(decode2_instru->arg3_addr!=-1)
        {
            if(rename_table[decode2_instru->arg3_addr]!=-1)
            {
                decode2_instru->arg3_addr=rename_table[decode2_instru->arg3_addr];
                decode2_instru->arg3=phy_R[decode2_instru->arg3_addr];
                decode2_instru->arg3_valid_bit=phy_R_status[decode2_instru->arg3_addr];
            }
                else
                {
					decode2_instru->arg3=R[decode2_instru->arg3_addr];
                    decode2_instru->arg3_addr=-1;
                    decode2_instru->arg3_valid_bit=0;
                }
        }


        //BZ / BNZ internal reg for introducing dependency
        if(decode2_instru->op_code==10 ||decode2_instru->op_code==11)
        {
            //if(rename_table[decode2_instru->arg1_addr]!=-1)
            {
                //decode2_instru->arg1_addr=rename_table[decode2_instru->arg1_addr];
                decode2_instru->arg1=phy_R[decode2_instru->arg1_addr];
                decode2_instru->arg1_valid_bit=phy_R_status[decode2_instru->arg1_addr];
            }
        }






        //copied for decode1 till ROB
        //for dest reg assign physical reg
        if(decode2_instru->op_code<9 || decode2_instru->op_code==13)
        {
            //no physical reg in free list
            if(l_free[0]==-1)
            {
                free_l_f=1;
                printf("STALL in decode stage 2 due to no physical reg in free list.\n");
                return -1;
            }
            else
            {
                //do everything to assign physical register to destination
                //update rename table, renamed array, alloc, phy_R_status, free list
                if(rename_table[decode2_instru->arg1_addr]!=-1)
                {
                    renamed[rename_table[decode2_instru->arg1_addr]]=1; //previous phy reg renamed
                    alloc[rename_table[decode2_instru->arg1_addr]]=0; //previous physical reg

                    /*put in free list when deallocated (when renamed and status bit valid
                        = when architectural reg written with that physical reg value). */
                }

                alloc[l_free[0]]=1; //mark allocated
                phy_R_status[l_free[0]]=1;  //mark invalid
                rename_table[decode2_instru->arg1_addr]=l_free[0];

                decode2_instru->arg1_addr=l_free[0];

                //shift l_free values and add -1 at end**** to handle it
                int j;
                for(j=0;j<16;j++)
                {
                    l_free[j] = l_free[j+1];
                }
                l_free[15] = -1;
            }
        }

        //put instru in ROB
        int i_ROB,i_IQ,i_LSQ;

        for(i_ROB=0;i_ROB<16;i_ROB++)
        {
            if(ROB[i_ROB]==NULL)
            {
                ROB[i_ROB]=decode2_instru;
                break;
            }
        }

        // put instruction in IQ and LSQ
        if(decode2_instru->op_code<8 || decode2_instru->op_code>9)
        {

            for(i_IQ=0;i_IQ<8;i_IQ++)
            {
                if(IQ[i_IQ]==NULL)
                {
                    IQ[i_IQ]=decode2_instru;
                    break;
                }
            }

            if((IQ[i_IQ]->op_code==10 || IQ[i_IQ]->op_code==11) && IQ[i_IQ]->arg1_valid_bit==1)
            {
                IQ[i_IQ]->arg1=phy_R[IQ[i_IQ]->arg1_addr];
                IQ[i_IQ]->arg1_valid_bit=phy_R_status[IQ[i_IQ]->arg1_addr];
            }
            if(IQ[i_IQ]->arg2_valid_bit==1)
            {
                IQ[i_IQ]->arg2=phy_R[IQ[i_IQ]->arg2_addr];
                IQ[i_IQ]->arg2_valid_bit=phy_R_status[IQ[i_IQ]->arg2_addr];
            }
            if(IQ[i_IQ]->arg3_valid_bit==1)
            {
                IQ[i_IQ]->arg3=phy_R[IQ[i_IQ]->arg3_addr];
                IQ[i_IQ]->arg3_valid_bit=phy_R_status[IQ[i_IQ]->arg3_addr];
            }
        }
        else
        {
            for(i_LSQ=0;i_LSQ<4;i_LSQ++)
            {
                if(LSQ[i_LSQ]==NULL)
                {
                    LSQ[i_LSQ]=decode2_instru;
                    break;
                }
            }

            if(LSQ[i_LSQ]->op_code==9 && LSQ[i_LSQ]->arg1_valid_bit==1)
            {
                LSQ[i_LSQ]->arg1=phy_R[LSQ[i_LSQ]->arg1_addr];
                LSQ[i_LSQ]->arg1_valid_bit=phy_R_status[LSQ[i_LSQ]->arg1_addr];
            }

            if(LSQ[i_LSQ]->arg2_valid_bit==1)
            {
                LSQ[i_LSQ]->arg2=phy_R[LSQ[i_LSQ]->arg2_addr];
                LSQ[i_LSQ]->arg2_valid_bit=phy_R_status[LSQ[i_LSQ]->arg2_addr];
            }

            if(LSQ[i_LSQ]->arg3_valid_bit==1)
            {
                LSQ[i_LSQ]->arg3=phy_R[LSQ[i_LSQ]->arg3_addr];
                LSQ[i_LSQ]->arg3_valid_bit=phy_R_status[LSQ[i_LSQ]->arg3_addr];
            }
        }
        //printf("   Decode 2:  %d:%d:%d:%d:%d:%d:%d:%d\n\n",decode2_instru->op_code,decode2_instru->arg1,decode2_instru->arg1_addr,decode2_instru->arg2,decode2_instru->arg2_addr,decode2_instru->arg3,decode2_instru->arg3_addr,decode2_instru->pc);
        return decode2_pc;
    }
}

void data_forwarding(){
    intsqueue();
    instlsq();
}

void intsqueue(){

    int i_IQ;
    for(i_IQ=0;i_IQ<8;i_IQ++)
    {

        if(IQ[i_IQ]!=NULL)
        {

        //check physical reg status (for data forwarding)

            if(IQ[i_IQ]->arg2_valid_bit==1 && IQ[i_IQ]->arg2_addr!=-1)
            {
                IQ[i_IQ]->arg2=phy_R[IQ[i_IQ]->arg2_addr];
                IQ[i_IQ]->arg2_valid_bit=phy_R_status[IQ[i_IQ]->arg2_addr];

            }
            if(IQ[i_IQ]->arg3_valid_bit==1 && IQ[i_IQ]->arg3_addr!=-1)
            {
                IQ[i_IQ]->arg3=phy_R[IQ[i_IQ]->arg3_addr];
                IQ[i_IQ]->arg3_valid_bit=phy_R_status[IQ[i_IQ]->arg3_addr];
            }

            //BZ / BNZ internal reg for introducing dependency
            if((IQ[i_IQ]->op_code==10 ||IQ[i_IQ]->op_code==11) && IQ[i_IQ]->arg1_valid_bit==1 && IQ[i_IQ]->arg1_addr!=-1)
            {
                    IQ[i_IQ]->arg1=phy_R[IQ[i_IQ]->arg1_addr];
                    IQ[i_IQ]->arg1_valid_bit=phy_R_status[IQ[i_IQ]->arg1_addr];
            }
        }
    }
}

void instlsq(){

    int i_LSQ;
    for(i_LSQ=0;i_LSQ<4;i_LSQ++)
    {

        if(LSQ[i_LSQ]!=NULL)
        {

        //check physical reg status (for data forwarding)
            if(LSQ[i_LSQ]->op_code==9 && LSQ[i_LSQ]->arg1_valid_bit==1 && LSQ[i_LSQ]->arg1_addr!=-1)
            {
                LSQ[i_LSQ]->arg1=phy_R[LSQ[i_LSQ]->arg1_addr];
                LSQ[i_LSQ]->arg1_valid_bit=phy_R_status[LSQ[i_LSQ]->arg1_addr];

            }
            if(LSQ[i_LSQ]->arg2_valid_bit==1 && LSQ[i_LSQ]->arg2_addr!=-1)
            {
                LSQ[i_LSQ]->arg2=phy_R[LSQ[i_LSQ]->arg2_addr];
                LSQ[i_LSQ]->arg2_valid_bit=phy_R_status[LSQ[i_LSQ]->arg2_addr];

            }
            if(LSQ[i_LSQ]->arg3_valid_bit==1 && LSQ[i_LSQ]->arg3_addr!=-1)
            {
                LSQ[i_LSQ]->arg3=phy_R[LSQ[i_LSQ]->arg3_addr];
                LSQ[i_LSQ]->arg3_valid_bit=phy_R_status[LSQ[i_LSQ]->arg3_addr];
            }
        }
    }
}

//main execute
int execute(){

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch  execute.\n\n");
        execute_instru=NULL;
        return -1;
    }

    //get instruction from IQ[0] rather than decode2_instru and remove that from IQ[0] and shift IQ
    //IQhead_instru=IQ[0];

    int IQindex_INT;
    int IQindex_MUL;
    int i_LSQ;

    IQhead_INT_instru=NULL;
    IQhead_MUL_instru=NULL;
    LSQhead_instru=NULL;

    for(IQindex_MUL=0;IQindex_MUL<8;IQindex_MUL++)
    {
        if(IQ[IQindex_MUL]!=NULL)
        {
            if(IQ[IQindex_MUL]->arg2_valid_bit!=1 && IQ[IQindex_MUL]->arg3_valid_bit!=1 && IQ[IQindex_MUL]->op_code==4)
            {
                    IQhead_MUL_instru=IQ[IQindex_MUL];
                    break;
            }
        }
    }

    for(IQindex_INT=0;IQindex_INT<8;IQindex_INT++)
    {
        if(IQ[IQindex_INT]!=NULL)
        {
            if((IQ[IQindex_INT]->op_code==10 || IQ[IQindex_INT]->op_code==11) && IQ[IQindex_INT]->arg1_valid_bit!=1)
            {
                IQhead_INT_instru=IQ[IQindex_INT];
                break;
            }
            else if(IQ[IQindex_INT]->op_code!=4 && IQ[IQindex_INT]->arg2_valid_bit!=1 && IQ[IQindex_INT]->arg3_valid_bit!=1)
            {
                IQhead_INT_instru=IQ[IQindex_INT];
                break;
            }
        }
    }

    i_LSQ=0;

    if(LSQ[i_LSQ]!=NULL)
    {
        if(LSQ[i_LSQ]->op_code==9)
        {
            if(LSQ[i_LSQ]->arg1_valid_bit!=1 && LSQ[i_LSQ]->arg2_valid_bit!=1 && LSQ[i_LSQ]->arg3_valid_bit!=1)
            {
                LSQhead_instru=LSQ[i_LSQ];
            }
        }
        else
        {
            if(LSQ[i_LSQ]->arg2_valid_bit!=1 && LSQ[i_LSQ]->arg3_valid_bit!=1)
            {
                LSQhead_instru=LSQ[i_LSQ];
            }
        }
    }


    //no instruction to get from decode
    if(IQhead_INT_instru==NULL && IQhead_MUL_instru==NULL && LSQhead_instru==NULL)
    {
        printf("No instructions to execute.\n\n");
        execute_instru=NULL;
        return -1;
    }

    //STORE - stall due to argument 1 invalid
	if(LSQhead_instru!=NULL && LSQhead_instru->op_code==9)
	{
        if(LSQhead_instru!=ROB[0])
        {
            printf("\nMemory 1 : STORE is not at ROB head.\n");
            execute_instru=NULL;
            LSQhead_instru=NULL;
        }
	}

    int execute_pc=-1;

    if(LSQhead_instru!=NULL && (LSQhead_instru->op_code==8||LSQhead_instru->op_code==9))
    {
            execute_pc=first_memory();
            pc_exe_mem1=execute_pc;
            execute_instru=memory1_instru;
    }

    if(install_f!=1 && IQhead_INT_instru!=NULL)
    {
        printf("\n in excute no stall ue to wb\n");
        execute_pc=oprexecute();
        pc_exe_int=execute_pc;
        execute_instru=int_instru;
    }

    if(IQhead_MUL_instru!=NULL && mul_occ_f!=1)
    {
        execute_pc=mulopr1();
        pc_exe_mul=execute_pc;
        execute_instru=mul1_instru;
        memory1_instru=NULL;
    }
/*
            else
            {
                printf("unknown instruction / STALL in execute.\n");
                execute_instru=NULL;
                return -1;
            }
*/

    return execute_pc;
}

//INT FU EXECUTE
int oprexecute(){

    //no instruction to get from decode
    if(install_f==1)
    {
        printf("STALL in execute INT due to write back occupied by memory inst.\n");
        int_instru=NULL;
        return -1;
    }

    if(IQhead_INT_instru==NULL)
    {
        printf("No instructions to oprexecute.\n\n");
        int_instru=NULL;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch  oprexecute.\n\n");
        int_instru=NULL;
        return -1;
    }

    //no stall
        if(dependency_check!=1)
        {

            //process instruction from decode to oprexecute stage
            int_instru=IQhead_INT_instru;
            int execute_int_pc=int_instru->pc-20000;


            //IQ shifting
            int IQ_index=0;
            for(IQ_index=0;IQ_index<7;IQ_index++)
            {
                if(IQ[IQ_index]==IQhead_INT_instru)
                    break;

            }
            for(;IQ_index<7;IQ_index++)
            {
                    IQ[IQ_index]=IQ[IQ_index+1];
            }
            IQ[7]=NULL;

           // printf("\nPC oprexecute:%d  Instruction: %s", execute_int_pc,instruction[execute_int_pc]);
            if(int_instru->op_code==0){
				int_instru->arg1=int_instru->arg2+int_instru->arg3;
			}
			else if(int_instru->op_code==1){
				int_instru->arg1=int_instru->arg2-int_instru->arg3;
			}
			else if(int_instru->op_code==2){
				int_instru->arg1=int_instru->arg2;
			}
			else if(int_instru->op_code==3){
				int_instru->arg1=int_instru->arg2;
			}
			else if(int_instru->op_code==5){
				int_instru->arg1=(int_instru->arg2&int_instru->arg3);
			}
			else if(int_instru->op_code==6){
				int_instru->arg1=(int_instru->arg2|int_instru->arg3);
			}
			else if(int_instru->op_code==7){
				int_instru->arg1=(int_instru->arg2^int_instru->arg3);
			}
			else if(int_instru->op_code==10){
				if(int_instru->arg1==0)
                    {
                        printf("\nint_instru->arg1:%d\n",int_instru->arg1);
                        if(int_instru->arg2>0) //mis-prediction
                        {
                            operation_bz(int_instru->arg2);
                            rollbacking();
                        }
                    }
                    else
                    {
                        if(int_instru->arg2<0)
                        {
                            rollbacking();
                            operation_bz(1);
                        }
                    }
			}
			else if(int_instru->op_code==11){
				if(int_instru->arg1!=0)
                    {
                        printf("\nint_instru->arg1:%d\n",int_instru->arg1);
                        if(int_instru->arg2>0) //mis-prediction
                        {
                            operation_bnz(int_instru->arg2);
                            rollbacking();
                        }
                    }
                    else
                    {
                        if(int_instru->arg2<0)
                        {
                            rollbacking();
                            operation_bnz(1);
                        }
                    }
			}
			else if(int_instru->op_code==12){
				operation_jump(int_instru->arg2,int_instru->arg3);
			}
			else if(int_instru->op_code==13){
				operation_bal(int_instru->arg2,int_instru->arg3);
			}
			else if(int_instru->op_code==14){
				
			}
			else{
				printf("Illegal token oprexecute.\n");
			}

            //reset reg status of dest reg for insts till LOAD
            if(int_instru->op_code<9 )
            {
                phy_R[int_instru->arg1_addr]=int_instru->arg1;
            }

            //printf("   Execute int: %d:%d:%d:%d:%d:%d:%d:%d\n\n",int_instru->op_code,int_instru->arg1,int_instru->arg1_addr,int_instru->arg2,int_instru->arg2_addr,int_instru->arg3,int_instru->arg3_addr,int_instru->pc);

			//branching with roll back
			if(int_instru->op_code==12 || int_instru->op_code==13)
                rollbacking();

			return execute_int_pc;
        }
        else
        {
            return -1;
        }

}

//MUL FU EXECUTE
int mulopr1(){

    //MUL non pipelined - already instruction in MUL FU
    if(mul_occ_f==1)
    {
        printf("STALL in non-pipelined execute MUL 1 as already inst executing in MUL FU.\n");
//        mul1_instru=NULL;
        return -1;
    }

    //no instruction to get from IQ

    if(IQhead_MUL_instru==NULL)
    {
        printf("No instructions to execute_mul 1.\n\n");
        mul1_instru=NULL;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch  execute_mul.\n\n");
        mul1_instru=NULL;
        return -1;
    }

//no stall
    if(dependency_check!=1)
    {
        //process instruction from decode to execute_mul stage
        mul1_instru=IQhead_MUL_instru;
        int execute_mul1_pc=mul1_instru->pc-20000;

        //IQ shifting
        int IQ_index=0;
        for(IQ_index=0;IQ_index<7;IQ_index++)
        {
            if(IQ[IQ_index]==IQhead_MUL_instru)
                break;

        }
        for(;IQ_index<7;IQ_index++)
        {
                IQ[IQ_index]=IQ[IQ_index+1];
        }
        IQ[7]=NULL;

        //printf("\nPC execute_mul 1:%d  Instruction: %s", execute_mul1_pc,instruction[execute_mul1_pc]);


        //printf("   Execute mul 1: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul1_instru->op_code,mul1_instru->arg1,mul1_instru->arg1_addr,mul1_instru->arg2,mul1_instru->arg2_addr,mul1_instru->arg3,mul1_instru->arg3_addr,mul1_instru->pc);
        return execute_mul1_pc;
    }
    else
    {
        return -1;
    }
}

//MUL FU EXECUTE
int mulopr2(){
    //no instruction to get from mul 1

    if(mul1_instru==NULL)
    {
        printf("No instructions in execute mul 2 to get from execute_mul 1.\n\n");
        mul2_instru=NULL;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch execute_mul 2.\n\n");
        mul2_instru=NULL;
        return -1;
    }

//no stall
    if(dependency_check!=1)
    {
        //process instruction from decode to execute_mul stage
        mul2_instru=mul1_instru;
        //mul1_instru=NULL;
        int execute_mul2_pc=mul2_instru->pc-20000;

       // printf("\nPC execute_mul 2:%d  Instruction: %s", execute_mul2_pc,instruction[execute_mul2_pc]);


        //printf("   Execute mul 2: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul2_instru->op_code,mul2_instru->arg1,mul2_instru->arg1_addr,mul2_instru->arg2,mul2_instru->arg2_addr,mul2_instru->arg3,mul2_instru->arg3_addr,mul2_instru->pc);
        return execute_mul2_pc;
    }
    else
    {
        return -1;
    }
}

//MUL FU EXECUTE
int mulopr3(){
    //no instruction to get from mul 1

    if(mul2_instru==NULL)
    {
        printf("No instructions in execute mul 3 to get from execute_mul 2.\n\n");
        mul3_instru=NULL;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch  execute_mul 3.\n\n");
        mul3_instru=NULL;
        return -1;
    }

//no stall
    if(dependency_check!=1)
    {
        //process instruction from decode to execute_mul stage
        mul3_instru=mul2_instru;
        mul2_instru=NULL;

        int execute_mul3_pc=mul3_instru->pc-20000;

        //printf("\nPC execute_mul 3:%d  Instruction: %s", execute_mul3_pc,instruction[execute_mul3_pc]);

        //printf("   Execute mul 3: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul3_instru->op_code,mul3_instru->arg1,mul3_instru->arg1_addr,mul3_instru->arg2,mul3_instru->arg2_addr,mul3_instru->arg3,mul3_instru->arg3_addr,mul3_instru->pc);
        return execute_mul3_pc;
    }
    else
    {
        return -1;
    }
}

//MUL FU EXECUTE
int mulopr4(){

    //no instruction to get from mul 3

    if(mul3_instru==NULL)
    {
        printf("No instructions to execute_mul 4.\n\n");
        mul4_instru=NULL;
        return -1;
    }

    if(mulstall_f==1)
    {
        printf("STALL in execute MUL 4 due to write back occupied.\n");
        mul4_instru=mul3_instru;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch  execute_mul 4.\n\n");
        mul4_instru=NULL;
        return -1;
    }

//no stall
    if(dependency_check!=1)
    {
        //process instruction from decode to execute_mul stage
        mul4_instru=mul3_instru;
        int execute_mul4_pc=mul4_instru->pc-20000;

        //printf("\nPC execute_mul 4:%d  Instruction: %s", execute_mul4_pc,instruction[execute_mul4_pc]);

        mul4_instru->arg1=mul4_instru->arg2*mul4_instru->arg3;

        //reset reg status of dest reg for insts till LOAD
        phy_R[mul4_instru->arg1_addr]=mul4_instru->arg1;

       // printf("   Execute mul 4: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul4_instru->op_code,mul4_instru->arg1,mul4_instru->arg1_addr,mul4_instru->arg2,mul4_instru->arg2_addr,mul4_instru->arg3,mul4_instru->arg3_addr,mul4_instru->pc);
        return execute_mul4_pc;
    }
    else
    {
        return -1;
    }
 }

//MEMORY FU 1 EXECUTE
int first_memory(){
    //no instruction to get from decode
    if(LSQhead_instru==NULL)
    {
        printf("No instructions to execute_memory.\n\n");
        memory1_instru=NULL;
        return -1;
    }

    //branching
    if(update_pc!=INT_MAX)
    {
        printf("STALL Due to branch  execute_memory.\n\n");
        memory1_instru=NULL;
        return -1;
    }

    //no stall
    if(dependency_check!=1)
    {
        //process instruction from decode to execute_memory stage
        memory1_instru=LSQhead_instru;
        int execute_memory1_pc=memory1_instru->pc-20000;

        //LSQ shifting
        int LSQ_index=0;
		while (LSQ_index<3){
			LSQ[LSQ_index]=LSQ[LSQ_index+1];
			LSQ_index++;
		}
        LSQ[4]=NULL;

        //printf("\nPC execute_memory 1:%d  Instruction: %s", execute_memory1_pc,instruction[execute_memory1_pc]);
        if(memory1_instru->op_code==8){
			memory1_instru->arg1=memory1_instru->arg2+memory1_instru->arg3;
		}
		else if(memory1_instru->op_code==9){
			memory1_instru->arg1=memory1_instru->arg2+memory1_instru->arg3;
		}
		else {
			printf("Illegal token execute_memory 1.\n");
		}

        //LOAD

       // printf("   Execute Memory 1: %d:%d:%d:%d:%d:%d:%d:%d\n\n",memory1_instru->op_code,memory1_instru->arg1,memory1_instru->arg1_addr,memory1_instru->arg2,memory1_instru->arg2_addr,memory1_instru->arg3,memory1_instru->arg3_addr,memory1_instru->pc);
        return execute_memory1_pc;
    }
    else
    {
        memory1_instru=NULL;
        return -1;
    }

}

//MEMORY FU 2 EXECUTE
int second_memory(){
        //no instruction to get from decode
        if(memory1_instru==NULL)
        {
            printf("No instructions to execute_memory 2.\n\n");
            memory2_instru=NULL;
            return -1;
        }

        //branching
        if(update_pc!=INT_MAX)
        {
            printf("STALL Due to branch  execute_memory 2.\n\n");
            memory2_instru=NULL;
            return -1;
        }

    //no stall
        if(dependency_check!=1)
        {

            //process instruction from decode to execute_memory stage
            memory2_instru=memory1_instru;
            memory1_instru=NULL;
            int execute_memory_pc=memory2_instru->pc-20000;

           //printf("\nPC execute_memory 2:%d  Instruction: %s", execute_memory_pc,instruction[execute_memory_pc]);

           // printf("   Execute Memory 2: %d:%d:%d:%d:%d:%d:%d:%d\n\n",memory2_instru->op_code,memory2_instru->arg1,memory2_instru->arg1_addr,memory2_instru->arg2,memory2_instru->arg2_addr,memory2_instru->arg3,memory2_instru->arg3_addr,memory2_instru->pc);
			return execute_memory_pc;
        }
        else
        {
            return -1;
        }

}

//MEMORY FU 3 EXECUTE
int third_memory(){
        //no instruction to get from decode
        if(memory2_instru==NULL)
        {
            printf("No instructions to execute_memory 3.\n\n");
            memory3_instru=NULL;
            return -1;
        }

        //branching
        if(update_pc!=INT_MAX)
        {
            printf("STALL Due to branch  execute_memory 3.\n\n");
            memory3_instru=NULL;
            return -1;
        }

    //no stall
        if(dependency_check!=1)
        {
            //process instruction from decode to execute_memory stage
            memory3_instru=memory2_instru;
            int execute_memory_pc=memory3_instru->pc-20000;

            if(memory3_instru->op_code==9){
                int i=0;
				while(i<15){
					ROB[i]=ROB[i+1];
					i++;
				}
                ROB[15]=NULL;
            }

            //printf("\nPC execute_memory 3:%d  Instruction: %s", execute_memory_pc,instruction[execute_memory_pc]);

            //LOAD
            if(memory3_instru->op_code==8)
            {
                //sanity check
                if((memory3_instru->arg1 < 0) || (memory3_instru->arg1 > 9999)){
                    printf("Memory 3 breach LOAD.\n");
                }
                else{
                    memory3_instru->arg1=v_memory[memory3_instru->arg1];
                    //printf("memory 3: %d\n",v_memory[memory3_instru->arg1]);
                }
            }

            //STORE
            if(memory3_instru->op_code==9)
            {
                //sanity check
                if((memory3_instru->arg1 < 0) || (memory3_instru->arg1 > 9999)){
                    printf("Memory 3 breach STORE.\n\n\n\n\n");
                }
                else{
                    v_memory[memory3_instru->arg1]=phy_R[memory3_instru->arg1_addr];
                }
            }

            //reset reg status of dest reg for insts till LOAD
            if(memory3_instru->op_code==8)
            {
                phy_R[memory3_instru->arg1_addr]=memory3_instru->arg1;
            }

           // printf("   Execute Memory 3: %d:%d:%d:%d:%d:%d:%d:%d\n\n",memory3_instru->op_code,memory3_instru->arg1,memory3_instru->arg1_addr,memory3_instru->arg2,memory3_instru->arg2_addr,memory3_instru->arg3,memory3_instru->arg3_addr,memory3_instru->pc);
			return execute_memory_pc;
        }
        else
        {
            return -1;
        }

}

//WRITE BACK stage
int write_back(){

	//get next instruction from one of multiple FUs

    if(memory3_instru!=NULL && memory3_instru->op_code==8)
    {
        //printf("\ngonna write memory\n");
        wb_instru=memory3_instru;
        memory3_instru=NULL;
        install_f=1;
        mulstall_f=1;
    } else if(int_instru!=NULL)
    {
        //printf("\ngonna write int\n");
        wb_instru=int_instru;
        int_instru=NULL;
        mulstall_f=1;
        install_f=0;
    }
    else if(mul4_instru!=NULL)
    {
        //printf("\ngonna write mul\n");

        install_f=0;
        mulstall_f=0;

        wb_instru=mul4_instru;
        mul4_instru=NULL;
        mul3_instru=NULL;
        mul2_instru=NULL;
        mul1_instru=NULL;

        mul_occ_f=0;
    }
    else
    {
        printf("No instructions to write back.\n\n");
        wb_instru=NULL;
        mulstall_f=0;
        install_f=0;
        return -1;
    }


	int wb_pc=wb_instru->pc-20000;

    //printf("\nPC write back:%d  Instruction: %s\n", wb_pc,instruction[wb_pc]);

    if(wb_instru->op_code<9 || wb_instru->op_code==13)
    {
        phy_R_status[wb_instru->arg1_addr]=0; //valid now - can be used by new
        printf("Tag for data forwarding: %d\n",wb_instru->arg1_addr);
        printf("Value forwarded: %d\n\n",phy_R[wb_instru->arg1_addr]);
    }

    data_forwarding();

    wb_instru=NULL;
    return wb_pc;
}

//commit stage
int commit(){
    //no instructions to get from write back stage

    install_f=0;
    mulstall_f=0;

	if(ROB[0]==NULL)
	{
        //printf("No instructions to commit.\n");
		commit_instru=NULL;
		return -1;
	}

    //in case of HALT, free pointers and exit
    if(ROB[0]->op_code==14)
    {
        quit();
        //printf("\n**********Terminating bcoz of HALT**********\n\n");
        display();
        printf("\nNumber of cycles done: %d\n",cycles_completed);
        exit(0);
    }


    if(ROB[0]->op_code>9 && ROB[0]->op_code<13)
    {
        commit_instru=ROB[0];
        int commit_pc=commit_instru->pc-20000;
        printf("\nCommit:%s",instruction[commit_pc]);
        int i;
        for(i=0;i<15;i++)
        {
            ROB[i]=ROB[i+1];
        }
        ROB[15]=NULL;
        commit_instru=NULL;
        return commit_pc;
    }

    if( (ROB[0]->op_code==13 || ROB[0]->op_code<9) && phy_R_status[ROB[0]->arg1_addr]==0)
    {
        wb_instru=NULL;
        commit_instru=ROB[0];

        int i;
        for(i=0;i<15;i++)
        {
            ROB[i]=ROB[i+1];
        }
        ROB[15]=NULL;

        //process next inst from write back

        int commit_pc=commit_instru->pc-20000;

        //printf("dependent_reg=%d\n",dependent_reg);
        //printf("commit_instru->arg1_addr= %d\n",commit_instru->arg1_addr);


        //remove dependency dependency flag & reg
        if(dependent_reg==commit_instru->arg1_addr )
        {
            dependency_check = 0;
            dependent_reg = -1;
            //printf("dependency_check=%d\n",dependency_check);
        }


        if((commit_instru->op_code==13 ||commit_instru->op_code<9) && phy_R_status[commit_instru->arg1_addr]==0)
        {
            printf("phy_R = %d\n",phy_R[commit_instru->arg1_addr]);
            if(commit_instru->arf_addr==8)
            {
                X=phy_R[commit_instru->arg1_addr];
            }
            else
            {
                if(commit_instru->arf_addr>-1)
                {
                    R[commit_instru->arf_addr]=phy_R[commit_instru->arg1_addr];
                }
            }
           // printf("\nCommit Registers updated\n");

            for(i=0;i<16;i++)
            {
                if(l_free[i]==-1)
                {
                    l_free[i]=commit_instru->arg1_addr;
                    break;
                }
            }
            alloc[commit_instru->arg1_addr]=0;
            if(renamed[commit_instru->arg1_addr]==0)
            {
                rename_table[commit_instru->arf_addr]= -1;
            }
            //printf("\nCommit Renaming structres updated\n");
        }
        commit_instru=NULL;
        return commit_pc;
    }
    else
    {
        commit_instru=NULL;
		return -1;
	}

}

//display menu choice
void display(){
	int i=0;

	if(fetch1_p==-1)
	{
		printf("No instructions in fetch stage 1.\n");
	}
	else
	{
		printf("Instruction in fetch stage 1: %s\n",instruction[fetch1_p]);
	}
	
	if(fetch2_p==-1)
	{
		printf("No instructions in fetch stage 2.\n");
	}
	else
	{
		printf("Instruction in fetch stage 2: %s\n",instruction[fetch2_p]);
	}
	
	if(decode1_p==-1)
	{
		printf("No instructions in decode stage 1.\n");
	}
	else
	{
		printf("Instruction in decode stage 1: %s\n",instruction[decode1_p]);
	}
	
	if(decode2_p==-1)
	{
		printf("No instructions in decode stage 2.\n");
	}
	else
	{
		printf("Instruction in decode stage 2: %s\n",instruction[decode2_p]);
	}
	
	if(pc_exe_int==-1)
	{
		printf("No instructions in int stage.\n");
	}
	else
	{
		printf("Instruction in int stage: %s\n",instruction[pc_exe_int]);
	}
	
	if(pc_exe_mem1==-1)
	{
		printf("No instructions in memory 1 stage.\n");
	}
	else
	{
		printf("Instruction in memory 1: %s\n",instruction[pc_exe_mem1]);
	}
	
	if(mem2_p==-1)
	{
		printf("No instructions in memory 2 stage.\n");
	}
	else
	{
		printf("Instruction in memory 2: %s\n",instruction[mem2_p]);
	}
	
	if(mem3_p==-1)
	{
		printf("No instructions in memory 3 stage.\n");
	}
	else
	{
		printf("Instruction in memory 3: %s\n",instruction[mem3_p]);
	}
	
	if(pc_exe_mul==-1)
	{
		printf("No instructions in mul 1 stage.\n");
	}
	else
	{
		printf("Instruction in mul 1: %s\n",instruction[pc_exe_mul]);
	}
	
	if(mul2_p==-1)
	{
		printf("No instructions in mul 2 stage.\n");
	}
	else
	{
		printf("Instruction in mul 2: %s\n",instruction[mul2_p]);
	}
	
	if(mul3_p==-1)
	{
		printf("No instructions in mul 3 stage.\n");
	}
	else
	{
		printf("Instruction in mul 3: %s\n",instruction[mul3_p]);
	}
	
	if(mul4_p==-1)
	{
		printf("No instructions in mul 4 stage.\n");
	}
	else
	{
		printf("Instruction in mul 4: %s\n",instruction[mul4_p]);
	}
	
	if(wb_p==-1)
	{
		printf("No instructions in write back stage.\n");
	}
	else
	{
		printf("Instruction in write back: %s\n",instruction[wb_p]);
	}
	
	if(commit_p==-1)
	{
		printf("No instructions in commit stage.\n");
	}
	else
	{
		printf("Instruction in commit: %s\n",instruction[commit_p]);
	}

    printf("\n\nIQ Entries:");
	i=0;
    while(i<8)
    {
        if(IQ[i]!=NULL)
        {
            printf("IQ[%d]= %s\n",i,instruction[IQ[i]->pc-20000]);
        }
		i++;
    }
    printf("\nLSQ Entries:");
	i=0;
    while(i<4)
    {
        if(LSQ[i]!=NULL)
        {
            printf("LSQ[%d]= %s\n",i,instruction[LSQ[i]->pc-20000]);
        }
		i++;
    }
    printf("\nROB Entries:\n");
	i=0;
    while(i<16)
    {
        if(ROB[i]!=NULL)
        {
            printf("ROB[%d]= %s\n",i,instruction[ROB[i]->pc-20000]);
        }
		i++;
    }
	
	printf("\nArchitectural Registers:\n");
	i=0;
	while(i<8)
	{
		printf("R[%d]:%d  ",i,R[i]);
		i++;
	}
	printf("X: %d\n",X);

    //Physical registers
	printf("\n\nPhysical Registers:\n");
	i=0;
	while(i<16)
	{
		printf("phy_R[%d]:%d:%d  ",i,phy_R[i],phy_R_status[i]);
		i++;
		if((i+1)%4==0)
			printf("\n");
	}

    //l_free[16];
	printf("\n\nFree List\n");
	i=0;
	while(i<16)
	{
		printf("[%d]:%d  ",i,l_free[i]);
		i++;
		if((i+1)%4==0)
			printf("\n");
	}

    //alloc[16];
	printf("\n\nAllocation List.\n");
	i=0;
   	while(i<16)
	{
		printf("alloc[%d]:%d  ",i,alloc[i]);
		i++;
		if((i+1)%4==0)
			printf("\n");
	}

    //renamed[16];
    printf("\n\nRenamed:\n");
	i=0;
   	while(i<16)
	{
		printf("[%d]:%d  ",i,renamed[i]);
		i++;
		if((i+1)%4==0)
			printf("\n");
	}

	//rename_table[9];
	printf("\n\nRename Table:\n");
	i=0;
	while(i<9)
	{
		printf("R[%d]:P[%d]  ",i,rename_table[i]);
		i++;
	}

    printf("\n\nMemory matrix: \n");
	//print memory matrix
	i=0;
	while(i<20)
	{
		printf("Memory :[%d]:%d  ",i,v_memory[i]);
		i++;
		if((i+1)%5==0)
			printf("\n");
	}
}

//simulate menu choice
void simulate(int num_cycl){
    //reset program counters
   pc_reset();

    execute_pc_set();

    while(num_cycl!=0)
    {
        commit_p=commit();
        wb_p=write_back();

        mem3_p=third_memory();
        mem2_p=second_memory();

        mul4_p=mulopr4();
        mul3_p=mulopr3();
        mul2_p=mulopr2();

        exe_p=execute();
        //intsqueue();
        decode2_p=second_decode();
        decode1_p=first_decode();
        fetch2_p=second_fetch();
        fetch1_p=first_fetch();

        //total no. of cycles done
        if(halt_f!=1) //if halt clock frozen
            cycles_completed++;

        num_cycl--;

//		printf("Cycles : %d\n\n",num_cycl);

       // printf("\n**************\n");
    }
    display();
}

//main func for user choice menu
int main(){
	char *tok,choice[15],tempcmd[9];
	int num_cycles=0;
	memset(tempcmd,'\0',sizeof(tempcmd));
	printf("\t\t\t---------------------------APEX Simulator------------------------------\n");

    //call initialize once in the beginning

	while(1){
        //printf("\n-----------------------\n");
		printf("Enter command : ");
		gets(choice);
		//printf("\n-----------------------\n");


		if(strcmp(choice,"initialize")==0){
			initialize();
		}

		else if(strcmp(choice,"display")==0){
			display();
		}

		else if(strcmp(choice,"exit")==0){
			return 1;
		}

		else{
			strncpy(tempcmd,choice,8);
			if((strcmp(tempcmd,"simulate")==0) && (choice[8]==' '))
			{
				tok = strtok(choice," ");
				tok = strtok(NULL," ");
				num_cycles = atoi(tok);
				simulate(num_cycles);
				printf("\nCycles_done: %d\n",cycles_completed);
			}

			else
			{
				printf("Wrong Input\n");
			}
		}

	}
	quit();
	return 0;
}
