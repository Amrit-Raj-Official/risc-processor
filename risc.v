`timescale 1ns / 1ps

//------------------------------------------------------------------------------

// Structural modules

//slt
module nslt#(parameter n =1) (input [n-1:0]x, y, output [n-1:0] r3);
    wire[n-1:0] sum;
    wire carry;
    wire V;
    full_adder #(n) subtrac(x,y,1'b1,sum,carry,V);
    assign r3 = sum[n-1];
endmodule

/* Subtractor, no longer needed
module subt#(parameter n = 1)(input [n-1:0] x, y, output [n-1:0] diff,output V);
        wire carry;
        wire [n-1:0]ytwos;
        twoscomp #(n) tc(y,ytwos);
        full_adder #(n) adder(x, ytwos,diff,carry,V);
endmodule*/

module add_str(input x, y, cin, output s, cout);
    wire s1,c1,c2,c3;
    xor(s1, x, y);
    xor(s, cin, s1);
    and(c1, x, y);
    and(c2, y, cin);
    and(c3, x, cin);
    or(cout, c1, c2, c3);
endmodule

module not_str #(parameter n =1 )(output [n-1:0] out, input [n-1:0] A);
    not not1[n-1:0](out,A);
endmodule

module full_adder#(parameter n = 1)(input [n-1:0] a, input [n-1:0] b, input carryin, output [n-1:0] sum, output carry, V);
    wire [n:0]cin;
    wire[n-1:0] b2;
    wire [n-1:0]invertb;
    not_str #(n) n1(invertb, b);
    mux_str #(n) mux1(b2, b, invertb, carryin);
    assign cin[0]= carryin;
    genvar i;
    generate
        for (i = 0; i<n;i=i+1)
        begin
            add_str fa(a[i],b2[i],cin[i],sum[i],cin[i+1]);
        end
    endgenerate
    wire cin_invert;
    not(cin_invert, cin[n]);
    mux_str #(1) mux2(carry, cin[n],cin_invert,carryin);
    xor(V, cin[n], cin[n-1]);
endmodule

module twoscomp#(parameter n = 1)(input [n-1:0]x, output [n-1:0]y);
    wire [n-1:0] ones;
    wire [n-1:0] one;
    wire [n-1:0] inverted;
    assign one = 1'b1;
    assign ones = {n{1'b1}};
    xor_str #(n) n_xor(inverted, x, ones);
    full_adder #(n) adder(inverted, one, 1'b0, y, carry, V);
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

module mux8_str #(parameter n = 1) (output [n - 1:0] out, input [n - 1:0] A, B,
C, D, E, F, G, H, input [2:0] sel);
    wire [n - 1:0] w1, w2, w3, w4, w5, w6;
    mux_str #(n) mux1(w1, A, B, sel[0]);
    mux_str #(n) mux2(w2, C, D, sel[0]);
    mux_str #(n) mux3(w5, w1, w2, sel[1]);
    mux_str #(n) mux4(w3, E, F, sel[0]);
    mux_str #(n) mux5(w4, G, H, sel[0]);
    mux_str #(n) mux6(w6, w1, w2, sel[1]);
    mux_str #(n) mux7(out, w5, w6, sel[2]);
endmodule

//------------------------------------------------------------------------------

// IF: Instruction Fetch

module PC(output reg [5:0] out, input [5:0] in, input clk);
    initial out = 6'b000000;
    always @(posedge clk)
        out <= in;
endmodule

module add_PC (output [5:0] out, input [5:0] A);
    wire Cout, V;
    full_adder #(6) alu_full_adder(A, 6'b000001, 1'b0, out, Cout, V);
endmodule

module memory(output [15:0] data_out, input [15:0] data_in,
input [5:0] data_addr, input read, load, stall);
    reg [15:0] inst_mem [0:63];
    reg [15:0] data_mem [0:15];
    integer i;
    initial begin
        for (i = 0; i < 64; i = i + 1)
            inst_mem[i] = 16'hFFFF;
        for (i = 0; i < 16; i = i + 1)
            data_mem[i] = 16'h0000;
        $readmemh("inst.dat", inst_mem);
        $readmemh("mem.dat", data_mem);
    end
    assign data_out = (read) ? data_mem[data_addr] : inst_mem[data_addr];
    always @(*)
        if (load & stall)
            data_mem[data_addr] <= data_in;
endmodule

// TODO: stall condition checking
module hazard(output stall1, output reg stall2, input [3:0] opcode, input clk);
    reg [1:0] state;
    assign stall1 = (state > 0) ? 1 : 0;
    initial begin
        state <= 0;
        stall2 <= 0;
    end
    always @(posedge clk) begin
        if (state == 0) begin
            case (opcode)
                4'h2: state <= 2'b10;
                4'h6: state <= 2'b10;
                4'h0: state <= 2'b10;
                4'h1: state <= 2'b10;
                4'h7: state <= 2'b10;
                4'h8: state <= 2'b10;
                4'hA: state <= 2'b10;
                4'hE: state <= 2'b10;
                default: state <= 2'b00;
            endcase
            // if (opcode == 4'hE) state <= 2'b10;
            // else if ()
        end else begin
            case (state)
                2'b01: begin
                    state <= 2'b00;
                    stall2 <= 0;
                end
                2'b10: begin
                    state <= 2'b01;
                    stall2 <= 1;
                end
                2'b11: state <= 2'b10;
                default: state <= 2'b00;
            endcase
        end
    end
endmodule

//------------------------------------------------------------------------------

// ID: Instruction Decode

module IF_ID(output reg [15:0] id_inst, id_data, output reg [5:0] id_pc,
input [15:0] if_inst, if_data, input [5:0] if_pc, input clk);
    initial begin
        id_inst = 16'hFFFF;
        id_data = 16'hFFFF;
        id_pc = 0;
    end
    always @(posedge clk) begin
        id_inst <= if_inst;
        id_data <= if_data;
        id_pc <= if_pc;
    end
endmodule

module controller(output reg [2:0] ALUControl, output reg ALUSrc, Branch,
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
                ALUControl <= 3'b000;
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
input [3:0] Aaddr, Baddr, Caddr, input load, clear, clk);
    integer i;
    reg [15:0] register [0:15];
    assign A = register[Aaddr];
    assign B = register[Baddr];
    assign reg1 = register[1];
    assign reg2 = register[2];
    assign reg3 = register[3];
    initial for (i = 0; i < 16; i = i + 1)
        register[i] <= 0;
    always @(posedge clk) begin
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
output reg [5:0] ex_pc, output reg [2:0] ex_ALUControl, output reg ex_ALUSrc,
ex_Branch, ex_MemRead,ex_MemtoReg, ex_MemWrite, ex_RegDst, ex_RegWrite,
input [15:0] id_inst,id_data1_out, id_data2_out, input [5:0] id_pc,
input [2:0] id_ALUControl, input id_ALUSrc, id_Branch,id_MemRead, id_MemtoReg,
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

module alu(output [15:0] out, output Cin, Cout, lt, eq, gt, V, zero,
    input [15:0] X, Y, input [2:0] opcode);
    wire [15:0] add_result;
    wire [15:0] sub_result;
    wire [15:0] and_result;
    wire [15:0] or_result;
    wire [15:0] slt_result;

    full_adder #(16) alu_full_adder(X, Y, 1'b0, add_result, Cout, V);
    full_adder #(16) alu_full_adder_sub(X, Y, 1'b1, sub_result, Cout, V);
    and_str #(16) alu_and(and_result, X, Y);
    or_str #(16) alu_or(or_result, X, Y);
    nslt #(16) alu_slt(X, Y, slt_result);
    mux8_str #(16) mux(out, add_result, sub_result, and_result, or_result,
        slt_result, sub_result, 16'h0000, 16'h0000, opcode);

    assign lt = X < Y;
    assign eq = X == Y;
    assign gt = X > Y;
    assign Cin = 0;
    assign zero = (out == 0) ? 1 : 0;
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

module MIPS(input clk, output [5:0] PC, output [15:0] R1, R2, R3);
    wire [15:0] temp;

    wire [15:0] if_inst, id_inst, ex_inst;
    wire [15:0] if_data, id_data;
    wire [15:0] if_inst_mux;
    wire [5:0] if_muxtopc1;
    wire [5:0] if_muxtopc2;
    wire [5:0] if_pc_next;
    wire [5:0] if_pc, id_pc, ex_pc;
    wire [5:0] if_mem_addr;
    wire if_stall1;
    wire if_stall2;

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

    wire [15:0] wb_write_data;

    wire [2:0] id_ALUControl, ex_ALUControl;
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
    wire carry;
    wire v;

    assign R1 = id_reg1;
    assign R2 = id_reg2;
    assign R3 = id_reg3;
    assign PC = if_pc;

    // IF
        PC if_PC(if_pc, if_muxtopc2, clk);

        mux_str #(6) if_mux1(if_muxtopc1, if_pc_next, mem_branch_addr,
            mem_PCSrc);
        add_PC if_add_PC(if_pc_next, if_pc);
        memory if_memory(if_data, ex_data2_out, if_mem_addr, if_stall2,
            ex_MemWrite, if_stall2);
        hazard if_hazard(if_stall1, if_stall2, if_data[15:12], clk);
        mux_str #(6) if_mux2(if_muxtopc2, if_muxtopc1, if_pc, if_stall1);
        mux_str #(16) if_mux3(if_inst_mux, if_data, 16'hDDDD,
            if_stall1 | mem_PCSrc);
        mux_str #(6) if_mux4(if_mem_addr, if_pc, {2'b00, ex_alu_out[3:0]},
            if_stall2);

    // ID
        IF_ID if_id(id_inst, id_data, id_pc, if_inst_mux, if_data, if_pc, clk);

        controller id_controller(id_ALUControl, id_ALUSrc, id_Branch,
            id_MemRead, id_MemtoReg, id_MemWrite, id_RegDst, id_RegWrite,
            id_inst[15:12]);
        reg_file id_reg_file(id_data1_out, id_data2_out, id_reg1, id_reg2,
            id_reg3, wb_write_data, id_inst[11:8], id_inst[7:4], wb_write_addr,
            wb_RegWrite, 1'b1, clk);

    // EX
        ID_EX id_ex(ex_inst, ex_data1_out, ex_data2_out, ex_pc, ex_ALUControl,
            ex_ALUSrc, ex_Branch, ex_MemRead, ex_MemtoReg, ex_MemWrite,
            ex_RegDst, ex_RegWrite, id_inst, id_data1_out, id_data2_out, id_pc,
            id_ALUControl, id_ALUSrc, id_Branch, id_MemRead, id_MemtoReg,
            id_MemWrite, id_RegDst, id_RegWrite, clk);

        full_adder #(6) ex_add(ex_pc, {{2{ex_inst[3]}}, ex_inst[3:0]}, 1'b0,
            ex_branch_addr, carry, v);
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
            wb_RegWrite, id_data, mem_alu_out, mem_write_addr,
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
    MIPS uut(clk, PC, R1, R2, R3);
    always #5 clk = ~clk;
    initial begin
        $display("time    clk    PC    R1    R2    R3");
        $monitor("%4d    %3d    %2d    %2d    %2d    %2d", $time, clk, PC, R1, R2, R3);
        clk = 0;
        wait (PC == 10) $finish;
    end
endmodule
