15-122 Principles of Imperative Computation
The C0VM

==========================================================

Useful information:
   c0vm-ref.txt           - Bytecode implementation reference

==========================================================

Compiling a C0 program to create a .bc0 file (produces tests/iadd.bc0):
   % cc0 -b tests/chararrays.c0

Compiling and running your C0VM implementation (with -DDEBUG)
(Must compile iadd.c0 to iadd.bc0 first)
   % make
   % ./c0vmd tests/chararrays.bc0

Compiling and running your C0VM implementation (without -DDEBUG)
(Must compile iadd.c0 to iadd.bc0 first)
   % make
   % ./c0vm tests/iadd.bc0

==========================================================
