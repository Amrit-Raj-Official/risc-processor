`timescale 1ns / 1ps

//------------------------------------------------------------------------------

// Structural modules

module and_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B);
    and and1[n - 1:0](out, A, B);
endmodule

module or_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B);
    or or1[n - 1:0](out, A, B);
endmodule

module xor_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B);
    xor xor1[n - 1:0](out, A, B);
endmodule

module mux_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B, input sel);
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

module add_gen #(parameter n = 4) (output [n - 1:0] out, input signed [n - 1:0] A, B);
    assign out = A + B;
endmodule

//------------------------------------------------------------------------------

// IF: Instruction Fetch

module PC(output reg [5:0] out, input [5:0] in, input clk);
    initial out = 6'b000000;
    always @(posedge clk)
        out <= in;
endmodule

module add_1 (output [5:0] out, input [5:0] A);
    assign out = A + 1;
endmodule

//------------------------------------------------------------------------------

// ID: Instruction Decode

module controller(output reg [3:0] ALUControl, output reg ALUSrc, Branch, MemRead, MemtoReg, MemWrite, RegDst, RegWrite, input [3:0] opcode, input clk);
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

module reg_file(output [15:0] A, B, reg1, reg2, reg3, input [15:0] C, input [3:0] Aaddr, Baddr, Caddr, input load, clear, clk);
    integer i;
    reg [15:0] register [0:15];
    assign A = register[Aaddr];
    assign B = register[Baddr];
    assign reg1 = register[1];
    assign reg2 = register[2];
    assign reg3 = register[3];
    initial for (i = 0; i < 16; i = i + 1)
        register[i] <= 0;
    always @(posedge clk or negedge clear) begin
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

module alu(output reg [15:0] out, output Cin, Cout, lt, eq, gt, V, zero, input [15:0] X, Y, input [3:0] opcode);
    reg signed [15:0] signed_X;
    reg signed [15:0] signed_Y;
    assign lt = X < Y;
    assign eq = X == Y;
    assign gt = X > Y;
    assign Cin = 0;
    assign Cout = 0;
    assign V = 0;
    assign zero = (out == 0) ? 0 : 1;
    always @(*) begin
        case (opcode)
            3'b000: // unsigned addition
                out <= X + Y;
            3'b001: begin// signed addition/subtraction
                signed_X = X;
                signed_Y = Y;
                out <= X + Y;
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

module memory(output [15:0] Rdata, inst, input [15:0] Wdata, data_addr, input [5:0] inst_addr, input read, load, clk);
    reg [15:0] inst_mem [0:63];
    reg [15:0] data_mem [0:15];
    initial begin
        $readmemh("inst.dat", inst_mem);
        $readmemh("mem.dat", data_mem);
    end
    assign inst = inst_mem[inst_addr];
    assign Rdata = (read) ? data_mem[data_addr[3:0]] : Rdata;
    always @(posedge clk) begin
        if (load)
            data_mem[data_addr[3:0]] <= Wdata;
    end
endmodule

//------------------------------------------------------------------------------

// Top level:

module MIPS(output [15:0] R1, R2, R3, output [5:0] PC, input clk);
    wire [15:0] inst;
    wire [15:0] reg1;
    wire [15:0] reg2;
    wire [15:0] reg3;
    wire [5:0] muxtopc;
    wire [5:0] pc_curr;
    wire [5:0] pc_next;

    wire [15:0] data1_out;
    wire [15:0] data2_out;
    wire [15:0] muxtoalu;
    wire [15:0] alu_out;
    wire [15:0] write_data;
    wire [5:0] branch_addr;
    wire [3:0] write_addr;

    wire [15:0] mem_data_out;

    wire [3:0] ALUControl;
    wire ALUSrc;
    wire Branch;
    wire MemRead;
    wire MemtoReg;
    wire MemWrite;
    wire PCSrc;
    wire RegDst;
    wire RegWrite;

    wire alu_cin;
    wire alu_cout;
    wire alu_lt;
    wire alu_eq;
    wire alu_gt;
    wire alu_v;
    wire alu_zero;
    wire reg_clear;

    assign R1 = reg1;
    assign R2 = reg2;
    assign R3 = reg3;
    assign PC = pc_curr;

    // IF
    mux_str #(6) if_mux(muxtopc, pc_next, branch_addr, PCSrc);
    PC if_pc(pc_curr, muxtopc, clk);
    add_1 if_add1(pc_next, pc_curr);

    // ID
    controller id_controller(ALUControl, ALUSrc, Branch, MemRead, MemtoReg, MemWrite, RegDst, RegWrite, inst[15:12], clk);
    reg_file id_reg_file(data1_out, data2_out, reg1, reg2, reg3, write_data, inst[11:8], inst[7:4], write_addr, RegWrite, 1'b1, clk);

    // EX
    add_gen #(6) ex_add(branch_addr, pc_next, {{2{inst[3]}},inst[3:0]});
    mux_str #(16) ex_mux(muxtoalu, data2_out, inst[15:0], ALUSrc);
    alu ex_alu(alu_out, alu_cin, alu_cout, alu_lt, alu_eq, alu_gt, alu_v, alu_zero, data1_out, muxtoalu, ALUControl);
    mux_str #(4) ex_mux2(write_addr, inst[3:0], inst[7:4], RegDst);

    // MEM
    and_str #(1) mem_add(PCSrc, Branch, alu_zero);
    memory mem_memory(mem_data_out, inst, data2_out, alu_out, pc_curr, MemRead, MemWrite, clk);

    // WB
    mux_str #(16) wb_mux(write_data, alu_out, mem_data_out, MemtoReg);
endmodule

//------------------------------------------------------------------------------

// Test Fixture:

module MIPS_test();
    reg clk;
    wire [15:0] R1, R2, R3;
    wire [5:0] PC;
    MIPS uut(R1, R2, R3, PC, clk);
    always #5 clk = ~clk;
    initial begin
        $display("time    clk    PC    R1    R2    R3");
        $monitor("%4d    %3d    %2d    %2d    %2d    %2d", $time, clk, PC, R1, R2, R3);
        clk = 0;
        #500 $finish;
    end
endmodule
