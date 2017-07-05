qcc -source -D_MPI=8 falling.c 
mpicc -Wall -std=c99 -O2 -D_MPI=8 _falling.c -o falling -lm
