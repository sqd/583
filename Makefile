CC=clang -g -O0 -fopenmp

# Generic rules for detecting race in arbitrary file
%.out: %.bc
	opt -load cmake-build-debug/libopmrace.so -omprace < $< > /tmp/null

# Generic rules for compiling a source file to bytecode
%.bc: %.c
	${CC} -emit-llvm -c -o $@ $<

%.S: %.c
	${CC} -emit-llvm -S -o $@ $<

clean:
	rm -f *.bc *.S