# RISC Processor
Verilog implementation of a 16-bit RISC processor designed around a basic instruction set.

## Running the Processor
Instructions for the processor should be included in the `inst.dat` file in hexadecimal format. Data memory can also be pre-loaded into the processor in hexadecimal format by modifying the `mem.dat` file.

Assuming the Verilog simulator [Icarus][iverilog] is used, the processor can be compiled by moving to the directory of `risc.v` and running:

    iverilog risc.v
    
Once compiled, the processor can now be executed by running the command:
  
    vvp a.out

[iverilog]: http://iverilog.icarus.com
