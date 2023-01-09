#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include "subprogram.c"

#include <stdio.h>

#ifndef RES
#define RES 1
#endif 

struct fraction {
	unsigned int num; // The numerator.
	unsigned int den; // The denominator.
};

unsigned int nondet_uint();
void __CPROVER_assume(int x);
void __CPROVER_assert(int x, char y[]);

#define assert2(x, y) __CPROVER_assert(x, y)
#define assume(x) __CPROVER_assume(x)


unsigned int main() {

	unsigned int val = nondet_uint();
	assume(val == 1);
	val = incrby20(val);

	

	assert(val != 1);
	return 0;
}