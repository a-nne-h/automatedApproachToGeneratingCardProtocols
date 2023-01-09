#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#ifndef VALUE
#define VALUE 1
#endif

unsigned int incrby20(unsigned int val) {
	for (int j = 0; j < 10; j++) {
		val = val + VALUE;
	}
	struct fraction frac;
	frac.num = 1;
	assert(VALUE == 1);
	return val;
}