#ifndef simulator
#define simulator

#define instructs 500


enum operation{
	ADD,
	SUB,
	MOVC,
    MOV,
	MUL,
	AND,
	OR,
	EX_OR,
	LOAD,
	STORE,
	BZ,
	BNZ,
	JUMP,
	BAL,
	HALT,
};

char *operate[]={"ADD","SUB","MOVC","MOV","MUL","AND","OR","EX-OR","LOAD","STORE","BZ","BNZ","JUMP","BAL","HALT"};


//data structure of an instruction
struct instru_info{
	enum operation op_code;
	int arg1;
	int arg1_addr;  //will hold phy_R address
	int arf_addr;   //to update R in end
	int arg1_valid_bit;
	int arg2;
	int arg2_addr;
	int arg2_valid_bit;
	int arg3;
	int arg3_addr;
	int arg3_valid_bit;
	int pc;
};


void pc_reset();
void flag_set_0();
void execute_pc_set();
void rollbacking();
void info_ptr_set();
void quit();
void operation_bz(int lit);
void operation_bnz(int lit);
void operation_jump(int reg,int lit);
void operation_bal(int reg,int lit);
int inst_components();
void initialize();
int first_fetch();
int second_fetch();
int first_decode();
int second_decode();
void data_forwarding();
void intsqueue();
void instlsq();
int execute();
int oprexecute();
int mulopr1();
int mulopr2();
int mulopr3();
int mulopr4();
int first_memory();
int second_memory();
int third_memory();
int write_back();
int commit();
void display();
void simulate(int num_cycl);

#endif
