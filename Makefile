lorenz: gcg_digraph.o
	gcc -o lorenz gcg_digraph.o -L. -lpthread -lc -larpack -llapack -lblas -lm -lgfortran
gcg_digraph.o: gcg_digraph.c
	gcc -c gcg_digraph.c -O0 -g -o gcg_digraph.o
clean:
	rm gcg_digraph.o
	rm lorenz
