
module ALUcontrol ( ALUop,  fun,  ALUctr);

input wire [1:0] ALUop;    // output from cntrol unit
input wire [5:0] fun;     // function which is from digit 0 to digit 5 in the instruction
output reg [3:0] ALUctr;  //ALU cntrol which is input to ALU

always @(ALUop or fun)
begin
case(ALUop)
  2'b10:case(fun)  // ALUop code for the R format
          6'b100000: ALUctr= 4'b0010;   // function=32 add alu operation
          6'b100100: ALUctr= 4'b0000;   // function=36  and alu operation
          6'b100101: ALUctr= 4'b0001;   // function=37  or alu operation
          6'b000000: ALUctr= 4'b0011;   // function=0  sll alu operation
          6'b100010: ALUctr= 4'b0110;   // function=34 sub alu operation
          default: ALUctr =4'bx;
        endcase 
  2'b00: ALUctr= 4'b0010;  // ALUop code for sw and lw; the alu should make add
  2'b01: ALUctr= 4'b0110;  // ALUop code for beg ; the alu should make sub
  default: ALUctr =4'b1111;                                                            
endcase
end	
endmodule 
//-----------------------------------------------------------------
module ALU(data1, data2, ALUctl, shamt, result, zeroFlag);
input wire signed [31:0] data1, data2;
input [4:0] shamt;
input [3:0] ALUctl;
output zeroFlag;
output signed [31:0] result;
parameter AND = 4'b0000, OR = 4'b0001, add = 4'b0010, sub = 4'b0110, slt = 4'b0111, NOR = 4'b1100, sll = 4'b0011;
assign result =
(ALUctl == AND)? data1&data2:
(ALUctl == OR)?  data1|data2:
(ALUctl == add)? data1+data2:
(ALUctl == sub)? data1-data2:
(ALUctl == NOR)? ~(data1&data2):
(ALUctl == sll)? data2 << shamt :
(ALUctl == slt)? ((data1 < data2)? 1:0):
32'bx;
assign zeroFlag = (data1 == data2)? 1:0;
endmodule
//-------------------------------------------------------------
module ControlUnit (opcode,RegDes,Branch,MemRead,MemtoReg,MemWrite,Aluop,Alusrc,RegWrite);



input wire[5:0]opcode;
output reg RegDes,Branch,MemtoReg,MemWrite,Alusrc,RegWrite,MemRead;
output reg[1:0] Aluop;

parameter Rformate = 6'b000000
,lw = 6'b100011

  ,sw = 6'b101011

  ,beq= 6'b000100;

  
initial Branch<=0;  
always @(opcode)
begin

case(opcode)
 Rformate: 
begin
RegDes=1'b1;
Branch=1'b0;
MemtoReg=1'b0;
 MemWrite=1'b0; 
 Alusrc=1'b0; 
RegWrite=1'b1; 
 MemRead=1'b0;
Aluop<=2'b10 ;
end
 lw: 
begin
RegDes<=1'b0;Branch<=1'b0;MemtoReg<=1'b1; MemWrite<=1'b0; Alusrc<=1'b1; RegWrite<=1'b1 ;   MemRead<=1'b1;
 Aluop<=2'b00 ;
end
sw: 
begin
RegDes<=1'bx;Branch<=1'b0;MemtoReg<=1'bx; MemWrite<=1'b1;  Alusrc<=1'b1; RegWrite<=1'b0;    MemRead<=1'b0;
Aluop<=2'b00 ;
 end
beq: 
begin
RegDes=1'bx;Branch=1'b1;MemtoReg=1'bx; MemWrite=1'b0; Alusrc<=1'b0; RegWrite<=1'b0;    MemRead<=1'b0;
Aluop<=2'b01;
end

endcase
end
endmodule
//----------------------------------------------------------------
module data_memory (read_data,clk,mem_read,mem_write,write_data,address);

  input wire clk,mem_read,mem_write ;
  input wire [31:0]write_data;
  input  wire signed [31:0]address;
  output wire [31:0]read_data;
  reg [31:0]ram[0:1023];
  wire [9:0] address_shifted;
  assign address_shifted=address[11:2];

  always @(posedge clk)
    begin
      if(mem_write)
        begin
          ram[address_shifted]<=write_data;
        end
    end
  assign read_data=(mem_read==1)?ram[address_shifted]:32'd0;                                 //I think 32'bx
endmodule
//----------------------------------------------------------------------------
module InstrMemory ( Address,  Instruction) ;

input [31:0] Address ;
output [31:0] Instruction ;
reg [31:0] Imem [0:1023] ;
wire [9:0] Address_shifted;
assign Address_shifted=Address[11:2];
initial
begin
$readmemb("Binary.txt",Imem) ;
end
assign Instruction= Imem[Address_shifted] ;
endmodule
//--------------------------------------------------------------------------------
module mux2x1_32 (in0,in1,out,sel);

input [31:0] in1,in0;
input sel;
output [31:0] out;


assign out=(sel==1)?in1:in0;                                         


endmodule

module mux2x1_5 (in0,in1,out,sel);

input [4:0] in1,in0;
input sel;
output [4:0] out;


assign out=(sel==1)?in1:in0;                                        



endmodule
module mux2x1_9 (in0,in1,out,sel1,sel2);

input [8:0] in1,in0;
input sel1,sel2;
output [8:0] out;


assign out=((sel1==1) || (sel2==1) )?in1:in0;                                         


endmodule
//-----------------------------------------------------------
module mux3x1_32 (in0,in1,in2,out,sel);

input [31:0] in1,in0,in2;
input [1:0] sel;
output [31:0] out;


assign out=(sel==0)?in0:((sel==1)?in1:in2);

endmodule
//------------------------------------------------------------
module pc (input wire[31:0] pc_in,input pchold, output reg [31:0] pc_out, input clk);
initial
begin
pc_out<= 0;
end
always @ (posedge clk)
begin
if(pchold == 0)
pc_out<=pc_in;
end


endmodule 
//--------------------------------------------------------------
module Regs(ReadReg1,ReadReg2,WriteReg,Aout,Bout,WriteData,WriteEnable,clk);

input wire [4:0]ReadReg1,ReadReg2,WriteReg;
input wire [31:0] WriteData;
input wire WriteEnable,clk;
output wire [31:0] Aout,Bout;
reg [31:0] Registers [0:31];
integer i;
initial
begin
    for(i=0;i<32;i=i+1)
    begin
      Registers[i]=i;
    end
end

always @(negedge clk)
begin

  if (WriteEnable == 1)
  begin
    Registers[WriteReg]= WriteData;
  end

end

assign  Aout = Registers[ReadReg1];
assign  Bout = Registers[ReadReg2];


endmodule

//----------------------------------------------------------------------------
module if_id( clk,hold,extendedpc,instruction,ifidir,ifidpc);
input clk,hold;  
input [31:0] extendedpc;
input [31:0] instruction;
output reg[31:0]ifidir;
output reg[31:0]ifidpc;
    
always@(posedge clk)
begin
if(hold == 0)
begin       
       ifidir<=instruction;
       ifidpc<=extendedpc;
end
end
 
endmodule

//------------------------------------------------------------------------------
module id_ex( clk,flag,data1,data2,ifidir,ifidpc,flagout,idexir,idexa,idexb,idexpc,Aluop,Alusrc,MemRead,MemWrite,MemtoReg,RegWrite,RegDes,Branch,Aluop_out,Alusrc_out,MemRead_out,MemWrite_out,MemtoReg_out,RegWrite_out,RegDes_out,Branch_out);
input clk,flag;
input Alusrc,MemRead,MemWrite,MemtoReg,RegWrite,RegDes,Branch;
input[1:0] Aluop;
input[31:0] data1,data2;
input[31:0]ifidir,ifidpc;
output reg [1:0] Aluop_out;
output reg Alusrc_out;
output reg MemRead_out;
output reg MemWrite_out;
output reg MemtoReg_out;
output reg RegWrite_out;
output reg RegDes_out;
output reg Branch_out;
output reg flagout;
output reg [31:0]idexir;
output reg [31:0]idexpc;
output reg [31:0]idexa;
output reg [31:0]idexb;

always@(posedge clk)
begin

Aluop_out<=Aluop;
Alusrc_out<=Alusrc;
RegWrite_out<=RegWrite;
MemRead_out<=MemRead;
MemWrite_out<=MemWrite;
MemtoReg_out<=MemtoReg;
RegDes_out<=RegDes;
Branch_out<=Branch;
idexir<=ifidir;
idexpc<=ifidpc;
idexa<=data1;
idexb<=data2;
flagout<=flag;

end
endmodule
//--------------------------------------------------------------------------

module ex_mem(clk,idexir,idexb,exmemaluout,exmemir,exmemb,zeroFlag,zeroFlagOut,AluResult,RegWriteDes,exmemRegWriteDesOut,beqPC,beqPCout,MemRead,MemWrite,Branch,RegWrite,MemtoReg,MemRead_out,MemWrite_out,RegWrite_out,MemtoReg_out,Branch_out);
input clk,MemRead,MemWrite,RegWrite,MemtoReg,Branch,zeroFlag;
input [31:0] idexir,idexb,beqPC,AluResult;
input[4:0] RegWriteDes;
output reg MemRead_out;
output reg MemWrite_out;
output reg RegWrite_out;
output reg MemtoReg_out;
output reg Branch_out;
output reg zeroFlagOut;
output reg [31:0]beqPCout;
output reg [31:0]exmemaluout;
output reg [31:0]exmemir;
output reg [31:0]exmemb;
output reg [4:0]exmemRegWriteDesOut;  

always@(posedge clk)
begin
MemRead_out<=MemRead;
MemWrite_out<=MemWrite;
RegWrite_out<= RegWrite;
MemtoReg_out<=MemtoReg;
Branch_out<=Branch;
zeroFlagOut<=zeroFlag;
exmemir<=idexir;
exmemb<=idexb;
exmemaluout<=AluResult;
beqPCout<=beqPC;
exmemRegWriteDesOut<=RegWriteDes;
end

endmodule
//---------------------------------------------------------------------------
module mem_wr(clk,DmemoryResult,exmemRegWriteDes,memwbRegWriteDes,exmemaluout,exmemir,memwraluout,memwrvalue,memwrir,MemtoReg,RegWrite,MemtoReg_out,RegWrite_out);
input clk,MemtoReg,RegWrite;
input [31:0] exmemaluout;
input [31:0] exmemir;
input [31:0] DmemoryResult;
input [4:0] exmemRegWriteDes;
output reg MemtoReg_out;
output reg RegWrite_out;
output reg [31:0] memwrvalue;
output reg [31:0] memwrir;
output reg [31:0] memwraluout;
output reg [4:0] memwbRegWriteDes;

always@(posedge clk)
begin

MemtoReg_out<=MemtoReg;
RegWrite_out<=RegWrite;
memwrvalue<=DmemoryResult;
memwraluout<=exmemaluout;
memwrir<=exmemir;
memwbRegWriteDes<=exmemRegWriteDes;
      
end
endmodule
//-----------------------------------------------------------------------------------------------
module HazardUnit(IFIDRs,IFIDRt,IDEXRt,IDEXMemRead,PCHold,IFIDHold,HazMuxCon);
 input [4:0] IFIDRs,IFIDRt,IDEXRt;
 input IDEXMemRead;	
 output reg PCHold, IFIDHold, HazMuxCon;
 initial
begin
PCHold <= 0;
IFIDHold <= 0;
HazMuxCon <= 0;
end

 always@(IFIDRs,IFIDRt,IDEXRt,IDEXMemRead)
 begin
if(IDEXMemRead && ((IDEXRt == IFIDRs)||(IDEXRt == IFIDRt)))
 begin//stall
   PCHold <= 1;
   IFIDHold <= 1;
   HazMuxCon <= 1;
 end
 else
 begin//no stall
    PCHold <= 0;
    IFIDHold <= 0;
    HazMuxCon <= 0;
 end
 end
endmodule 
//--------------------------------------------------------------------------
module Comparator_beq(data1,data2,result);
input [31:0] data1;
input [31:0] data2;
output reg result;
always@(data1 or data2)
begin
if(data1 == data2)
result <= 1;
else
result <= 0;
end
endmodule
//--------------------------------------------------------------------------
module beq_pc_flusher(pcsrc,controlmux);
input pcsrc;

output reg controlmux;

always@(pcsrc)
begin
if(pcsrc == 1)
begin
controlmux<=1;
end
else
controlmux<=0;
end
endmodule
//---------------------------------------------------------------------------
module forwarding_unit(idexrs,idexrt,exmemrd,memwrrd,exmem_regwrite,memwr_regwrite,forwarda,forwardb);
  input exmem_regwrite;
  input [4:0] exmemrd;
  input [4:0] idexrs;
  input [4:0] idexrt;
  input memwr_regwrite;
  input [4:0] memwrrd;
  output reg[1:0] forwarda;
  output reg[1:0] forwardb;
initial
begin
forwarda <= 2'b00;
forwardb <= 2'b00;
end

always@(exmem_regwrite or exmemrd  or idexrt or idexrs or memwrrd or memwr_regwrite)
begin
if(exmem_regwrite&&(exmemrd==idexrs))
forwarda<= 2'b10;
else if(memwr_regwrite&&(memwrrd==idexrs))
forwarda<= 2'b01;
else
forwarda<=2'b00;
end
always@(exmem_regwrite or  exmemrd or idexrs or idexrt or memwrrd or memwr_regwrite)
begin
if(exmem_regwrite&&(exmemrd==idexrt))
forwardb<= 2'b10;
else if(memwr_regwrite&&(memwrrd==idexrt))
forwardb<= 2'b01;
else
forwardb<=2'b00;
end
endmodule
//--------------------------------------------------------------------------
/*module mips (input clk,input reset,output [31:0] Aluout,output [31:0] PC_out, output [31:0] Instr, output [31:0] Immediate_extend, output [31:0] PC_input);
wire [31:0] pc_input,pc_out;  
wire [31:0]instr;
wire [31:0]pc_regfile;

wire [5:0]opcode,fun;
wire [4:0] rs,rt,rd,shamt;
wire [15:0] immediate;
wire signed [31:0] immediate_extend;

assign opcode=instr[31:26];
assign fun=instr[5:0];
assign rs=instr[25:21];
assign rt=instr[20:16];
assign rd=instr[15:11];
assign shamt=instr[10:6];
assign immediate=instr[15:0];
assign immediate_extend={{16{instr[15]}},instr[15:0]};

wire [31:0] Readdata1_alu,Readdata2;
wire [31:0] ALUoutput;
wire [31:0] ALuscr_ALUinput2;

wire [31:0] MemReadData;
wire [4:0] RegDest_writeReg;

wire [31:0] MemtoReg_Writrdata;
wire [31:0] pcAdd4;
wire [31:0] beq_pc;
wire [31:0] immediate_extend_shifted;

wire RegDst,Branch,MemRead,MemtoReg,MemWrite,ALUscr,RegWrite,pcscr,zeroflag;
wire [1:0] ALUop;
wire [3:0] ALUctr_lines;

pc m(pc_input,pc_out,clk,reset);
InstrMemory irmem (pc_out,instr,reset);
Regs registerfile (rs,rt,RegDest_writeReg,Readdata1_alu,Readdata2,MemtoReg_Writrdata,RegWrite,clk,reset);
ALU alu(Readdata1_alu,ALuscr_ALUinput2,ALUctr_lines,shamt,ALUoutput,zeroflag);
data_memory Dmemory (MemReadData,clk,MemRead,MemWrite,Readdata2,ALUoutput);
mux2x1_5 regscr (rt,rd,RegDest_writeReg,RegDst);
mux2x1_32 Aluscr (Readdata2,immediate_extend,ALuscr_ALUinput2,ALUscr);
mux2x1_32 mem2reg (ALUoutput,MemReadData,MemtoReg_Writrdata,MemtoReg);
ControlUnit ctrunit(opcode,RegDst,Branch,MemRead,MemtoReg,MemWrite,ALUop,ALUscr,RegWrite);
ALUcontrol aluctr (ALUop,fun,ALUctr_lines);

assign pcAdd4=pc_out+4;
assign immediate_extend_shifted=immediate_extend<<2;
assign beq_pc=pcAdd4+immediate_extend_shifted;
assign pcscr=Branch&&zeroflag;

mux2x1_32 branch (pcAdd4,beq_pc,pc_input,pcscr);

assign Aluout=ALUoutput;
assign PC_out=pc_out ;
assign Instr= instr;
assign Immediate_extend=immediate_extend ;
assign PC_input=pc_input;

endmodule
*/
//-----------------------------------------------------------

module MIPS_PIPELINE(input clk,output [31:0] Aluout,output [31:0] PC_out, output [31:0] Instr, output [31:0] Immediate_extend, output [31:0] PC_input,
output [31:0] RegWriteData, output [4:0] RegWriteDEST,output [31:0] MEMValue ,output [31:0] ifidir , output [8:0] muxcontrolout, output ZeroToBeq, output PCSCR,
output [31:0] PCADD4,output [31:0] BEQPC,output [31:0] Immediate_Extend_Beq,output flagOut, output CtlMux,output[4:0] Rs,output[4:0] Rt,output[4:0] RD,
output [31:0] aluin1,output [31:0] aluin2,output [31:0]f,output [1:0] FORWARDA,output[1:0] FORWARDB,output [31:0] exmemalu,output [31:0] b);


wire [31:0] pc_input,pc_out;  
wire [31:0] instr;
wire [31:0] pcAdd4;
wire [31:0] IFIDIR;
wire [31:0] IFIDPC;
wire [31:0] IDEXIR;
wire [31:0] IDEXPC;
wire [31:0] IDEXA;
wire [31:0] IDEXB;
wire [31:0] EXMEMIR;
wire [31:0] EXMEMB;
wire [31:0] MEMWBIR;
wire [5:0] opcode,fun;
wire [4:0] rs,rt,rtToMul,rd,shamt;
wire [15:0] immediate;
wire signed [31:0] immediate_extend;
wire signed [31:0] immediate_extend_beq;
wire [4:0] WriteReg;
wire [31:0] Writedata;
wire [31:0] Readdata1,Readdata2;
wire RegDst,MemRead,MemtoReg,MemWrite,ALUscr,RegWrite,zeroflag;
wire Branch;
wire pcscr;
wire RegDstToIDEX,BranchToIDEX,MemReadToIDEX,MemtoRegToIDEX,MemWriteToIDEX,ALUscrToIDEX,RegWriteToIDEX;
wire RegDst_out_IDEX,Branch_out_IDEX,MemRead_out_IDEX,MemtoReg_out_IDEX,MemWrite_out_IDEX,ALUscr_out_IDEX,RegWrite_out_IDEX;
wire Branch_out_EXMEM,MemRead_out_EXMEM,MemtoReg_out_EXMEM,MemWrite_out_EXMEM,RegWrite_out_EXMEM,zeroFlagOut;
wire RegWrite_out_MEMWB,MemtoReg_out_MEMWB;
wire [1:0] ALUop;
wire [1:0] ALUopToIDEX;
wire [1:0] ALUop_out_IDEX;
wire [3:0] ALUctr_lines;
wire [31:0] ALUoutput;
wire [31:0] EXMEMALUoutput;
wire [31:0] MEMWBALUoutput;
wire [31:0] MEMWBvalue;
wire [31:0] ALUinput2;
wire [31:0] beq_pc;
wire [31:0] beqPCout;
wire [31:0] immediate_extend_shifted;
wire [31:0] immediate_extend_shifted_beq;
wire [4:0] RegisterDestination;
wire [4:0] RegisterDestinationEXMEM;
wire [4:0] RegisterDestinationMEMWB;
wire [31:0] MemReadData;
wire [8:0] ControlToMux;
wire [8:0] MuxControlOut;
wire pcHold,IFIDhold;
wire[8:0] ZeroToMux;
wire ControlMux;
wire Controlbeq;
wire FinalMuxControl;
wire zero_beq;
wire flagout;

//assign FinalMuxControl = ControlMux;// || Controlbeq;
assign opcode=IFIDIR[31:26];
assign fun=IDEXIR[5:0];
assign rs=IFIDIR[25:21];
assign rt=IFIDIR[20:16];
assign rtToMul=IDEXIR[20:16];
assign rd=IDEXIR[15:11];
assign shamt=IDEXIR[10:6];
assign immediate=IDEXIR[15:0];
assign immediate_extend={{16{IDEXIR[15]}},IDEXIR[15:0]};
assign immediate_extend_beq={{16{IFIDIR[15]}},IFIDIR[15:0]};
assign immediate_extend_shifted=immediate_extend<<2;
assign immediate_extend_shifted_beq=immediate_extend_beq<<2;
assign beq_pc=IFIDPC+immediate_extend_shifted_beq;
assign pcscr = BranchToIDEX&&zero_beq;
assign pcAdd4=pc_out+4;
//assign pcscr = 0;         //pcscr =0  to make pc not equal x
assign ControlToMux = {RegDst,Branch,MemRead,MemtoReg,MemWrite,ALUscr,RegWrite,ALUop};
assign ALUopToIDEX = MuxControlOut[1:0];
assign RegWriteToIDEX = MuxControlOut[2];
assign ALUscrToIDEX = MuxControlOut[3];
assign MemWriteToIDEX = MuxControlOut[4];
assign MemtoRegToIDEX = MuxControlOut[5];
assign MemReadToIDEX = MuxControlOut[6];
assign BranchToIDEX = MuxControlOut[7];
assign RegDstToIDEX = MuxControlOut[8];
assign ZeroToMux = 9'b000000000;
assign flagOut = flagout;
assign Rs=rs;
assign Rt=rt;
assign RD=RegisterDestination;
assign exmemalu = EXMEMALUoutput;
assign b = IDEXB;

//========forwarding================================================================
wire [4:0] IDEXrs,IDEXrt,EXMEMrd,MEMWBrd;
wire [1:0] forwarda,forwardb;
wire [31:0] ALU_inputA,forwardb_AluSrc;
assign IDEXrs=IDEXIR[25:21];
assign IDEXrt=IDEXIR[20:16];
assign EXMEMrd=EXMEMIR[15:11];
assign MEMWBrd=MEMWBIR[15:11];
forwarding_unit Forwarding(IDEXrs,IDEXrt,RegisterDestinationEXMEM,RegisterDestinationMEMWB,RegWrite_out_EXMEM,RegWrite_out_MEMWB,forwarda,forwardb);
mux3x1_32 forwarda_mux(IDEXA,Writedata,EXMEMALUoutput,ALU_inputA,forwarda);
mux3x1_32 forwardb_mux(IDEXB,Writedata,EXMEMALUoutput,forwardb_AluSrc,forwardb);
//====================================================================================


pc m(pc_input,pcHold,pc_out,clk);
InstrMemory irmem(pc_out,instr);
if_id IFIDRegister(clk,IFIDhold,pcAdd4,instr,IFIDIR,IFIDPC);
Regs registerfile (rs,rt,RegisterDestinationMEMWB,Readdata1,Readdata2,Writedata,RegWrite_out_MEMWB,clk);
ControlUnit ctrunit(opcode,RegDst,Branch,MemRead,MemtoReg,MemWrite,ALUop,ALUscr,RegWrite);
id_ex IDEXRegister(clk,pcscr,Readdata1,Readdata2,IFIDIR,beq_pc,flagout,IDEXIR,IDEXA,IDEXB,IDEXPC,ALUopToIDEX,ALUscrToIDEX,MemReadToIDEX,MemWriteToIDEX,MemtoRegToIDEX,RegWriteToIDEX,RegDstToIDEX,BranchToIDEX,ALUop_out_IDEX,ALUscr_out_IDEX,MemRead_out_IDEX,MemWrite_out_IDEX,MemtoReg_out_IDEX,RegWrite_out_IDEX,RegDst_out_IDEX,Branch_out_IDEX);
mux2x1_32 AluSrc (forwardb_AluSrc,immediate_extend,ALUinput2,ALUscr_out_IDEX);
ALUcontrol aluctr (ALUop_out_IDEX,fun,ALUctr_lines);
ALU alu(ALU_inputA,ALUinput2,ALUctr_lines,shamt,ALUoutput,zeroflag);
mux2x1_5 regDst (rtToMul,rd,RegisterDestination,RegDst_out_IDEX);
ex_mem EXMEMRegister(clk,IDEXIR,IDEXB,EXMEMALUoutput,EXMEMIR,EXMEMB,zeroflag,zeroFlagOut,ALUoutput,RegisterDestination,RegisterDestinationEXMEM,beq_pc,beqPCout,MemRead_out_IDEX,MemWrite_out_IDEX,Branch_out_IDEX,RegWrite_out_IDEX,MemtoReg_out_IDEX,MemRead_out_EXMEM,MemWrite_out_EXMEM,RegWrite_out_EXMEM,MemtoReg_out_EXMEM,Branch_out_EXMEM);
data_memory Dmemory (MemReadData,clk,MemRead_out_EXMEM,MemWrite_out_EXMEM,EXMEMB,EXMEMALUoutput);
mux2x1_32 branch (pcAdd4,beq_pc,pc_input,pcscr);
mem_wr MEMWBRegister(clk,MemReadData,RegisterDestinationEXMEM,RegisterDestinationMEMWB,EXMEMALUoutput,EXMEMIR,MEMWBALUoutput,MEMWBvalue,MEMWBIR,MemtoReg_out_EXMEM,RegWrite_out_EXMEM,MemtoReg_out_MEMWB,RegWrite_out_MEMWB);
mux2x1_32 mem2reg (MEMWBALUoutput,MEMWBvalue,Writedata,MemtoReg_out_MEMWB);
mux2x1_9 ControlToIDEX(ControlToMux,ZeroToMux,MuxControlOut,ControlMux,Controlbeq);
HazardUnit HU(rs,rt,RegisterDestination,MemRead_out_IDEX,pcHold,IFIDhold,ControlMux);
Comparator_beq C(Readdata1,Readdata2,zero_beq);
beq_pc_flusher F(flagout,Controlbeq);

assign Aluout=ALUoutput;
assign PC_out=pc_out;
assign Instr= instr;
assign Immediate_extend=immediate_extend;
assign Immediate_Extend_Beq=immediate_extend_beq;
assign PC_input=pc_input;
assign RegWriteData = Writedata;
assign RegWriteDEST = RegisterDestinationMEMWB; 
assign MEMValue = MemReadData;
assign ifidir = IFIDIR;
assign muxcontrolout = MuxControlOut;
assign ZeroToBeq = zero_beq;
assign PCADD4 = pcAdd4;
assign PCSCR = pcscr;
assign BEQPC = beq_pc;
assign CtlMux = ControlMux;
assign aluin1=ALU_inputA;
assign aluin2=ALUinput2;
assign f=IDEXA;
assign FORWARDA = forwarda;
assign FORWARDB = forwardb;


endmodule
//-----------------------------------------------------------------------------    

module test_Mips();
reg clk=0;   
wire signed [31:0] Aluout;
wire [31:0] PC_out;
wire [31:0] Instr;
wire [31:0] Read1;
wire [31:0] Read2;
wire signed [31:0] Immediate_extend;
wire signed [31:0] Immediate_Extend_Beq;

wire [31:0] PC_input;
wire [31:0] RegWriteData;
wire [4:0] RegWriteDEST;
wire [31:0] MEMValue; 
wire [31:0] ifidir;
wire [8:0] muxcontrol;
wire ZeroToBeq;
wire PCSCR;
wire [31:0]PCADD4;
wire [31:0]BEQPC;
wire flagout;
wire CtlMux;
wire[4:0]RS,RT,RD;
wire [31:0] aluin1,aluin2,f;
wire[1:0] forwarda,forwardb;
wire[31:0] exmem,b;
MIPS_PIPELINE MY_MIPS(clk, Aluout,PC_out, Instr, Immediate_extend, PC_input,RegWriteData, RegWriteDEST, MEMValue, ifidir,muxcontrol,ZeroToBeq,PCSCR,PCADD4,BEQPC,
Immediate_Extend_Beq,flagout,CtlMux,RS,RT,RD,aluin1,aluin2,f,forwarda,forwardb,exmem,b);

always
begin
#10
clk <= ~clk ;
end
initial
begin
$monitor($time,,,"clk:%d,Alu1:%d Alu2=%d Aluout:%d PC_out:%d Instr:%h PC_in:%d  WriteData:%d DEST:%d RS=%d RT=%d RD=%d  ",
clk,aluin1,aluin2,Aluout,PC_out,Instr,PC_input,RegWriteData,RegWriteDEST,RS,RT,RD);    
end
endmodule