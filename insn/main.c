#include <math.h>
#include <stdio.h>
#include <stdint.h>


uint32_t mul_dbl(double a, double b);

int main(int argc, char **argv)
{
	printf("foo: %d\n", mul_dbl(1.2, 2.3));
	printf("foo: %d\n", mul_dbl(1.2, 2.3e-312));
	printf("foo: %d\n", mul_dbl(1.2, INFINITY));

	return 0;
}
