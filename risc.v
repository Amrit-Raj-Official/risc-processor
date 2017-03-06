`timescale 1ns / 1ps

//------------------------------------------------------------------------------

// Structural modules

//slt
module nslt#(parameter n =1) (input [n-1:0]x, y, output [n-1:0] r3);
        wire[n-1:0] sum;
        wire carry;
        subt #(n) subtrac(x,y,sum);
        assign r3 = sum[n-1];
endmodule


//subtractor
module subt#(parameter n = 1)(input [n-1:0] x, y, output [n-1:0] diff);
        wire carry;
        wire [n-1:0]ytwos;
        twoscomp #(n) tc(y,ytwos);
        full_adder #(n) adder(x, ytwos,diff,carry);
endmodule

module add_str(input x, y, cin, output s, cout);
    wire s1,c1,c2,c3;
    xor(s1, x, y);
    xor(s, cin, s1);
    and(c1, x, y);
    and(c2, y, cin);
    and(c3, x, cin);
    or(cout, c1, c2, c3);
endmodule

module full_adder#(parameter n = 1)(input [n-1:0] a, b, output [n-1:0] sum, output carry);
    wire [n:0]cin;
    assign cin[0]= 1'b0;
    genvar i;
    generate
        for (i = 0; i<n;i=i+1)
        begin
            add_str fa(a[i],b[i],cin[i],sum[i],cin[i+1]);
        end
    endgenerate
    assign carry = cin[n];
endmodule

module twoscomp#(parameter n = 1)(input [n-1:0]x, output [n-1:0]y);
    wire [n-1:0] ones;
    wire [n-1:0] one;
    wire [n-1:0] inverted;
    assign one = 1'b1;
    assign ones = {n{1'b1}};
    xor_str #(n) n_xor(inverted, x, ones);
    full_adder #(n) adder(inverted, one, y, carry);
endmodule

module and_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B);
    and and1[n - 1:0](out, A, B);
endmodule

module or_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B);
    or or1[n - 1:0](out, A, B);
endmodule

module xor_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B);
    xor xor1[n - 1:0](out, A, B);
endmodule

module mux_str #(parameter n = 1) (output [n - 1:0] out,
input [n - 1:0] A, B, input sel);
    wire [n - 1:0] s1;
    wire [n - 1:0] s2;
    wire inv_sel;
    xor_str xor1(inv_sel, sel, 1'b1);
    and_str #(n) and1(s1, A, {n{inv_sel}});
    and_str #(n) and2(s2, B, {n{sel}});
    or_str #(n) or1(out, s1, s2);
endmodule

module unsigned_add_str();
endmodule

module signed_add_str();
endmodule

module complement_str();
endmodule

//------------------------------------------------------------------------------

// Generic modules (non-structural)

module add_gen #(parameter n = 4) (output [n - 1:0] out,
input signed [n - 1:0] A, B);
    assign out = A + B;
endmodule

//------------------------------------------------------------------------------

// IF: Instruction Fetch

module PC(output reg [5:0] out, input [5:0] in, input clk);
    initial out = 6'b000000;
    always @(posedge clk)
        out <= in;
endmodule

module add_PC (output [5:0] out, input [5:0] A);
    assign out = A + 1;
endmodule

module memory(output [15:0] data_out, Rdata, inst, input [15:0] Wdata,
data_addr, input [5:0] inst_addr, input read, load);
    reg [15:0] inst_mem [0:63];
    reg [15:0] data_mem [0:15];
    initial begin
        $readmemh("inst.dat", inst_mem);
        $readmemh("mem.dat", data_mem);
    end
    assign inst = inst_mem[inst_addr];
    assign Rdata = (read) ? data_mem[data_addr[3:0]] : inst_mem[inst_addr];
    assign data_out = (read) ? data_mem[data_addr[3:0]] : inst_mem[inst_addr];
    always @(*) begin
        if (load)
            data_mem[data_addr[3:0]] <= Wdata;
    end
endmodule

module hazard(output stall, input [3:0] opcode, input clk);
    reg [1:0] state;
    assign stall = (state > 0) ? 1 : 0;
    initial state <= 0;
    always @(posedge clk) begin
        if (state == 0) begin
            case (opcode)
                4'hE: state <= 2'b10;
                4'h2: state <= 2'b10;
                4'h6: state <= 2'b10;
                4'h0: state <= 2'b10;
                4'h1: state <= 2'b10;
                4'h7: state <= 2'b10;
                4'h8: state <= 2'b10;
                default: state <= 2'b00;
            endcase
        end else if (clk) begin
            case (state)
                2'b01: state <= 2'b00;
                2'b10: state <= 2'b01;
                2'b11: state <= 2'b10;
                default: state <= 2'b00;
            endcase
        end
    end
endmodule

//------------------------------------------------------------------------------

// ID: Instruction Decode

module IF_ID(output reg [15:0] id_inst, output reg [5:0] id_pc,
input [15:0] if_inst, input [5:0] if_pc, input clk);
    initial begin
        id_inst = 16'hFFFF;
        id_pc = 0;
    end
    always @(posedge clk) begin
        id_inst <= if_inst;
        id_pc <= if_pc;
    end
endmodule

module controller(output reg [3:0] ALUControl, output reg ALUSrc, Branch,
MemRead, MemtoReg, MemWrite, RegDst, RegWrite, input [3:0] opcode);
    initial begin
        ALUControl <= 0;
        ALUSrc <= 0;
        Branch <= 0;
        MemRead <= 0;
        MemtoReg <= 0;
        MemWrite <= 0;
        RegDst <= 0;
        RegWrite <= 0;
    end
    always @(opcode) begin
        case (opcode)
            4'h2: begin
                ALUControl <= 3'b001;
                ALUSrc <= 0;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 0;
                RegWrite <= 1;
            end
            4'h6: begin
                ALUControl <= 3'b101;
                ALUSrc <= 0;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 0;
                RegWrite <= 1;
            end
            4'h0: begin
                ALUControl <= 3'b010;
                ALUSrc <= 0;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 0;
                RegWrite <= 1;
            end
            4'h1: begin
                ALUControl <= 3'b011;
                ALUSrc <= 0;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 0;
                RegWrite <= 1;
            end
            4'h7: begin
                ALUControl <= 3'b100;
                ALUSrc <= 0;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 0;
                RegWrite <= 1;
            end
            4'h8: begin
                ALUControl <= 3'b000;
                ALUSrc <= 1;
                Branch <= 0;
                MemRead <= 1;
                MemtoReg <= 1;
                MemWrite <= 0;
                RegDst <= 1;
                RegWrite <= 1;
            end
            4'hA: begin
                ALUControl <= 3'b000;
                ALUSrc <= 1;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 1;
                RegDst <= 1;
                RegWrite <= 0;
            end
            4'hE: begin
                ALUControl <= 3'b101;
                ALUSrc <= 0;
                Branch <= 1;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 1;
                RegWrite <= 0;
            end
            default: begin
                ALUControl <= 3'b000;
                ALUSrc <= 0;
                Branch <= 0;
                MemRead <= 0;
                MemtoReg <= 0;
                MemWrite <= 0;
                RegDst <= 0;
                RegWrite <= 0;
            end
        endcase
    end
endmodule

module reg_file(output [15:0] A, B, reg1, reg2, reg3, input [15:0] C,
input [3:0] Aaddr, Baddr, Caddr, input load, clear);
    integer i;
    reg [15:0] register [0:15];
    assign A = register[Aaddr];
    assign B = register[Baddr];
    assign reg1 = register[1];
    assign reg2 = register[2];
    assign reg3 = register[3];
    initial for (i = 0; i < 16; i = i + 1)
        register[i] <= 0;
    always @(*) begin
        if (!clear)
            for (i = 0; i < 16; i = i + 1)
                register[i] <= 0;
        else
            if (load)
                register[Caddr] <= C;
    end
endmodule

//------------------------------------------------------------------------------

// EX: Execute

module ID_EX(output reg [15:0] ex_inst, ex_data1_out, ex_data2_out,
output reg [5:0] ex_pc, output reg [3:0] ex_ALUControl, output reg ex_ALUSrc,
ex_Branch, ex_MemRead,ex_MemtoReg, ex_MemWrite, ex_RegDst, ex_RegWrite,
input [15:0] id_inst,id_data1_out, id_data2_out, input [5:0] id_pc,
input [3:0] id_ALUControl, input id_ALUSrc, id_Branch,id_MemRead, id_MemtoReg,
id_MemWrite, id_RegDst, id_RegWrite, input clk);
    initial begin
        ex_inst <= 16'hFFFF;
        ex_data1_out <= 0;
        ex_data2_out <= 0;
        ex_pc <= 0;
        ex_ALUControl <= 0;
        ex_ALUSrc <= 0;
        ex_Branch <= 0;
        ex_MemRead <= 0;
        ex_MemtoReg <= 0;
        ex_MemWrite <= 0;
        ex_RegDst <= 0;
        ex_RegWrite <= 0;
    end
    always @(posedge clk) begin
        ex_inst <= id_inst;
        ex_data1_out <= id_data1_out;
        ex_data2_out <= id_data2_out;
        ex_pc <= id_pc;
        ex_ALUControl <= id_ALUControl;
        ex_ALUSrc <= id_ALUSrc;
        ex_Branch <= id_Branch;
        ex_MemRead <= id_MemRead;
        ex_MemtoReg <= id_MemtoReg;
        ex_MemWrite <= id_MemWrite;
        ex_RegDst <= id_RegDst;
        ex_RegWrite <= id_RegWrite;
    end
endmodule

module alu(output reg [15:0] out, output Cin, Cout, lt, eq, gt, V, zero,
    input [15:0] X, Y, input [3:0] opcode);
    reg signed [15:0] signed_X;
    reg signed [15:0] signed_Y;
    assign lt = X < Y;
    assign eq = X == Y;
    assign gt = X > Y;
    assign Cin = 0;
    assign Cout = 0;
    assign V = 0;
    assign zero = (out == 0) ? 1 : 0;
    always @(*) begin
        case (opcode)
            3'b000: // unsigned addition
                out <= X + Y;
            3'b001: begin // signed addition/subtraction
                signed_X = X;
                signed_Y = Y;
                out <= signed_X + signed_Y;
            end
            3'b010: // "and"
                out <= X & Y;
            3'b011: // "or"
                out <= X | Y;
            3'b100: // set on less than
                out <= (X < Y) ? 1 : 0;
            3'b101: // branch if not equal
                out <= X - Y;
            default:
                out <= 0;
        endcase
    end
endmodule

//------------------------------------------------------------------------------

// MEM: Memory Access

module EX_MEM(output reg [15:0] mem_alu_out, mem_data2_out,
output reg [5:0] mem_branch_addr, output reg [3:0] mem_write_addr,
output reg mem_alu_zero, mem_Branch, mem_MemRead, mem_MemtoReg, mem_MemWrite,
mem_RegWrite, input [15:0] ex_alu_out, ex_data2_out,
input [5:0] ex_branch_addr, input [3:0] ex_write_addr, input ex_alu_zero,
ex_Branch, ex_MemRead, ex_MemtoReg, ex_MemWrite, ex_RegWrite, clk);
    initial begin
        mem_alu_out <= 0;
        mem_data2_out <= 0;
        mem_branch_addr <= 0;
        mem_write_addr <= 0;
        mem_alu_zero <= 0;
        mem_Branch <= 0;
        mem_MemRead <= 0;
        mem_MemtoReg <= 0;
        mem_MemWrite <= 0;
        mem_RegWrite <= 0;
    end
    always @(posedge clk) begin
        mem_alu_out <= ex_alu_out;
        mem_data2_out <= ex_data2_out;
        mem_branch_addr <= ex_branch_addr;
        mem_write_addr <= ex_write_addr;
        mem_alu_zero <= ex_alu_zero;
        mem_Branch <= ex_Branch;
        mem_MemRead <= ex_MemRead;
        mem_MemtoReg <= ex_MemtoReg;
        mem_MemWrite <= ex_MemWrite;
        mem_RegWrite <= ex_RegWrite;
    end
endmodule

//------------------------------------------------------------------------------

// WB: Write Back

module MEM_WB(output reg [15:0] wb_data_out, wb_alu_out,
output reg [3:0] wb_write_addr, output reg wb_MemtoReg, wb_RegWrite,
input [15:0] mem_data_out, mem_alu_out, input [3:0] mem_write_addr,
input mem_MemtoReg, mem_RegWrite, clk);
    initial begin
        wb_data_out <= 0;
        wb_alu_out <= 0;
        wb_write_addr <= 0;
        wb_MemtoReg <= 0;
        wb_RegWrite <= 0;
    end
    always @(posedge clk) begin
        wb_data_out <= mem_data_out;
        wb_alu_out <= mem_alu_out;
        wb_write_addr <= mem_write_addr;
        wb_MemtoReg <= mem_MemtoReg;
        wb_RegWrite <= mem_RegWrite;
    end
endmodule

//------------------------------------------------------------------------------

// Top level:

module MIPS(output [15:0] R1, R2, R3, output [5:0] PC, input clk);
    wire [15:0] if_inst, id_inst, ex_inst;
    wire [15:0] if_inst_mux;
    wire [5:0] if_muxtopc1;
    wire [5:0] if_muxtopc2;
    wire [5:0] if_pc_next;
    wire [5:0] if_pc, id_pc, ex_pc;
    wire if_stall;

    wire [15:0] id_reg1;
    wire [15:0] id_reg2;
    wire [15:0] id_reg3;
    wire [15:0] id_data1_out, ex_data1_out;
    wire [15:0] id_data2_out, ex_data2_out, mem_data2_out;

    wire [15:0] ex_muxtoalu;
    wire [15:0] ex_alu_out, mem_alu_out, wb_alu_out;
    wire [5:0] ex_branch_addr, mem_branch_addr;
    wire [3:0] ex_write_addr, mem_write_addr, wb_write_addr;

    wire [15:0] mem_data_out, ex_data_out, wb_data_out;
    wire [15:0] mem_temp;

    wire [15:0] wb_write_data;

    wire [3:0] id_ALUControl, ex_ALUControl;
    wire id_ALUSrc, ex_ALUSrc;
    wire id_Branch, ex_Branch, mem_Branch;
    wire id_MemRead, ex_MemRead, mem_MemRead;
    wire id_MemtoReg, ex_MemtoReg, mem_MemtoReg, wb_MemtoReg;
    wire id_MemWrite, ex_MemWrite, mem_MemWrite;
    wire id_RegDst, ex_RegDst;
    wire id_RegWrite, ex_RegWrite, mem_RegWrite, wb_RegWrite;
    wire mem_PCSrc;

    wire ex_alu_cin;
    wire ex_alu_cout;
    wire ex_alu_lt;
    wire ex_alu_eq;
    wire ex_alu_gt;
    wire ex_alu_v;
    wire ex_alu_zero, mem_alu_zero;
    wire reg_clear;

    assign R1 = id_reg3;
    assign R2 = if_stall;
    assign R3 = if_inst_mux;
    assign PC = if_pc;

    // IF
        PC if_PC(if_pc, if_muxtopc2, clk);

        mux_str #(6) if_mux1(if_muxtopc1, if_pc_next, mem_branch_addr, mem_PCSrc);
        add_PC if_add_PC(if_pc_next, if_pc);
        memory if_memory(mem_temp, mem_data_out, if_inst, mem_data2_out,
            mem_alu_out, if_pc, mem_MemRead, mem_MemWrite);
        hazard if_hazard(if_stall, if_inst[15:12], clk);
        mux_str #(6) if_mux2(if_muxtopc2, if_muxtopc1, if_pc, if_stall);
        mux_str #(16) if_mux3(if_inst_mux, if_inst, 16'hDDDD, if_stall | mem_PCSrc);

    // ID
        IF_ID if_id(id_inst, id_pc, if_inst_mux, if_pc, clk);

        controller id_controller(id_ALUControl, id_ALUSrc, id_Branch,
            id_MemRead, id_MemtoReg, id_MemWrite, id_RegDst, id_RegWrite,
            id_inst[15:12]);
        reg_file id_reg_file(id_data1_out, id_data2_out, id_reg1, id_reg2,
            id_reg3, wb_write_data, id_inst[11:8], id_inst[7:4], wb_write_addr,
            wb_RegWrite, 1'b1);

    // EX
        ID_EX id_ex(ex_inst, ex_data1_out, ex_data2_out, ex_pc, ex_ALUControl,
            ex_ALUSrc, ex_Branch, ex_MemRead, ex_MemtoReg, ex_MemWrite,
            ex_RegDst, ex_RegWrite, id_inst, id_data1_out, id_data2_out, id_pc,
            id_ALUControl, id_ALUSrc, id_Branch, id_MemRead, id_MemtoReg,
            id_MemWrite, id_RegDst, id_RegWrite, clk);

        add_gen #(6) ex_add(ex_branch_addr, ex_pc,
            {{2{ex_inst[3]}}, ex_inst[3:0]});
        mux_str #(16) ex_mux1(ex_muxtoalu, ex_data2_out, ex_inst[15:0],
            ex_ALUSrc);
        alu ex_alu(ex_alu_out, ex_alu_cin, ex_alu_cout, ex_alu_lt, ex_alu_eq,
            ex_alu_gt, ex_alu_v, ex_alu_zero, ex_data1_out, ex_muxtoalu,
            ex_ALUControl);
        mux_str #(4) ex_mux2(ex_write_addr, ex_inst[3:0], ex_inst[7:4],
            ex_RegDst);

    // MEM
        EX_MEM ex_mem(mem_alu_out, mem_data2_out, mem_branch_addr,
            mem_write_addr, mem_alu_zero, mem_Branch, mem_MemRead,
            mem_MemtoReg, mem_MemWrite, mem_RegWrite, ex_alu_out, ex_data2_out,
            ex_branch_addr, ex_write_addr, ex_alu_zero, ex_Branch, ex_MemRead,
            ex_MemtoReg, ex_MemWrite, ex_RegWrite, clk);

        and_str #(1) mem_and(mem_PCSrc, mem_Branch, ~mem_alu_zero);

    // WB
        MEM_WB mem_wb(wb_data_out, wb_alu_out, wb_write_addr, wb_MemtoReg,
            wb_RegWrite, mem_data_out, mem_alu_out, mem_write_addr,
            mem_MemtoReg, mem_RegWrite, clk);

        mux_str #(16) wb_mux(wb_write_data, wb_alu_out, wb_data_out,
            wb_MemtoReg);
endmodule

//------------------------------------------------------------------------------

// Test Bench:

module MIPS_test();
    reg clk;
    wire [15:0] R1, R2, R3;
    wire [5:0] PC;
    MIPS uut(R1, R2, R3, PC, clk);
    always #5 clk = ~clk;
    initial begin
        $display("time    clk    PC    R1    R2    R3");
        $monitor("%4d    %3d    %2d    %2d    %2d    %2h", $time, clk, PC, R1, R2, R3);
        clk = 0;
        #1000 $finish;
    end
endmodule
