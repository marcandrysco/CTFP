#include <stdio.h>
#include <emmintrin.h>
#include <stdio.h>
#include <math.h>
#include <alloca.h>

typedef double vec_t __attribute__((vector_size(32)));
typedef float v2f __attribute__((vector_size(8)));

volatile vec_t v[1024];
volatile vec_t v1, v2, v3, v4;

v2f bar(v2f a, v2f b)
{
	return a + b;
}

v2f bar2(v2f a, v2f b, v2f c)
{
	return a + b * c + c / a - (c * b * a);
}

double foo(double v)
{
	return sqrt(v);
}

int main(int argc, char **argv)
{
	/*
	int i, j;

	vec_t c = (vec_t){ 1.0, 2.0, 3.0, 4.0 };
	for(i = 0; i < 1024; i++) {
		v[i][0] = rand() / (double)RAND_MAX;
		v[i][1] = rand() / (double)RAND_MAX;
		v[i][2] = rand() / (double)RAND_MAX;
		v[i][3] = rand() / (double)RAND_MAX;
	}

	for(j = 0; j < 10000; j++) {
		for(i = 0; i < 1024; i++) {
			int j = rand() % 1024;
			int k = rand() % 1024;
			int l = rand() % 1024;
			int m = rand() % 1024;

			vec_t t1 = v[j] * v[k];
			vec_t t2 = v[k] / (c + v[m]);
			vec_t t3 = v[j] * v[l] * v[m];

			v[i] = t1 + t2 - t3;
		}
	}

	printf("%.2f, %.2f, %.2f, %.2f\n", v[0][0], v[0][1], v[0][2], v[0][3]);
	*/

	/*
	v1 = (vec_t){ 1.2, 3.4, 5.6, 7.8 };
	v2 = (vec_t){ 2.3, 4.5, 6.7, 8.9 };
	v3 = v1 - v2;

	printf("%.2f, %.2f, %.2f, %.2f\n", v3[0], v3[1], v3[2], v3[3]);
	printf("%.2f, %.2f, %.2f, %.2f\n", v1[0] - v2[0], v1[1] - v2[1], v1[2] - v2[2], v1[3] - v2[3]);

	v1 = (vec_t){ 1.2, 3.4, 5.6, 7.8 };
	v2 = (vec_t){ 2.3, 4.5, 6.7, 8.9 };
	v3 = v1 * v2;

	printf("%.2f, %.2f, %.2f, %.2f\n", v3[0], v3[1], v3[2], v3[3]);
	printf("%.2f, %.2f, %.2f, %.2f\n", v1[0] * v2[0], v1[1] * v2[1], v1[2] * v2[2], v1[3] * v2[3]);

	v1 = (vec_t){ 1.2, 3.4, 5.6, 7.8 };
	v2 = (vec_t){ 2.3, 4.5, 6.7, 8.9 };
	v3 = (vec_t){ 0.1, 2.3, 4.5, 6.7 };
	v4 = v1 + v2 * v3;

	printf("%.2f, %.2f, %.2f, %.2f\n", v4[0], v4[1], v4[2], v4[3]);
	printf("%.2f, %.2f, %.2f, %.2f\n", v1[0] + v2[0] * v3[0], v1[1] + v2[1] * v3[1], v1[2] + v2[2] * v3[2], v1[3] + v2[3] * v3[3]);

	v1 = (vec_t){ 1.2, 3.4, 5.6, 7.8 };
	v2 = (vec_t){ 2.3, 4.5, 6.7, 8.9 };
	v3 = (vec_t){ 0.1, 2.3, 4.5, 6.7 };
	v4 = v1 * v2 + v3;

	printf("%.2f, %.2f, %.2f, %.2f\n", v4[0], v4[1], v4[2], v4[3]);
	printf("%.2f, %.2f, %.2f, %.2f\n", v1[0] * v2[0] + v3[0], v1[1] * v2[1] + v3[1], v1[2] * v2[2] + v3[2], v1[3] * v2[3] + v3[3]);

	*/
	return 0;
}
