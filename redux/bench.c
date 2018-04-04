#include <stdint.h>
#include <string.h>


#define ATTR __attribute__((noinline))

#define DO_MANY(thing)  thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing \
                        thing thing thing thing  thing thing thing thing  thing thing thing thing  thing thing thing thing
//#define DO_MANY(thing)  thing 

#define PERF_INIT() do { \
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out)); \
		begin = perf_begin(); \
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out)); \
	} while(0)

#define PERF_DONE() do { \
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out)); \
		end = perf_end(); \
		asm volatile("" :: "x"(in1), "x"(in2), "x"(out)); \
	} while(0)

#define F32_DECL() float in1, in2, out, res; uint32_t begin, end;
#define F32_INIT(OP) do { in1 = src1f32; in2 = src2f32; OP; res = out; in1 = src1f32; in2 = src2f32; PERF_INIT(); } while (0)
#define F32_DO(OP) DO_MANY(do { OP; float t = xor_f32(out, res); in1 = xor_f32(t, in1); in2 = xor_f32(t, in2); } while(0);)
#define F32_DONE() do { PERF_DONE(); sinkf32 = out; return end - begin; } while (0)
#define F32_BENCH(NAM, OP) \
	static ATTR uint32_t NAM##_f32(void) { F32_DECL(); F32_INIT(OP); F32_DO(OP); F32_DONE(); } 

#define F64_DECL() double in1, in2, out, res; uint32_t begin, end;
#define F64_INIT(OP) do { in1 = src1f64; in2 = src2f64; OP; res = out; in1 = src1f64; in2 = src2f64; PERF_INIT(); } while (0)
#define F64_DO(OP) DO_MANY(do { OP; float t = xor_f64(out, res); in1 = xor_f64(t, in1); in2 = xor_f64(t, in2); } while(0);)
#define F64_DONE() do { PERF_DONE(); sinkf64 = out; return end - begin; } while (0)
#define F64_BENCH(NAM, OP) \
	static ATTR uint32_t NAM##_f64(void) { F64_DECL(); F64_INIT(OP); F64_DO(OP); F64_DONE(); } 
		

/*
 * local declarations
 */
static inline uint32_t perf_begin(void);
static inline uint32_t perf_end(void);

static inline float xor_f32(float left, float right);
static inline double xor_f64(double left, double right);

extern volatile float sinkf32, src1f32, src2f32;
extern volatile double sinkf64, src1f64, src2f64;


F32_BENCH(base, out = in1);
F32_BENCH(add, out = in1 + in2);
F32_BENCH(mul, out = in1 * in2);
F32_BENCH(div, out = in1 / in2);

F64_BENCH(base, out = in1);
F64_BENCH(add, out = in1 + in2);
F64_BENCH(mul, out = in1 * in2);
F64_BENCH(div, out = in1 / in2);


/**
 * Begin performance tracking.
 *   &returns: The clock count.
 */
static inline uint32_t perf_begin(void)
{
	uint32_t eax, edx;

	asm volatile(
		"rdtsc\n"
		"mov %%eax, %0\n"
		"mov %%edx, %1\n"
		: "=r"(eax), "=r"(edx)
		:
		: "%rax", "%rbx", "%rcx", "%rdx", "memory"
	);

	return eax;
}

/**
 * End performance tracking.
 *   &returns: The clock count.
 */
static inline uint32_t perf_end(void)
{
	uint32_t eax, edx;

	asm volatile(
		"rdtsc\n"
		"mov %%eax, %0\n"
		"mov %%edx, %1\n"
		: "=r" (eax), "=r"(edx)
		:
		: "%rax", "%rbx", "%rcx", "%rdx", "memory"
	);

	return eax;
}


/**
 * Xor two floats together.
 *   @left: The left float.
 *   @right: The right float.
 *   &returns: The xored version.
 */
static inline float xor_f32(float left, float right)
{
	float r;

	asm volatile("vxorps %1,%2,%0" : "=x"(r) : "x"(left), "x"(right));

	return r;

	float out;
	uint32_t v1, v2, v3;

	memcpy(&v1, &left, 4);
	memcpy(&v2, &right, 4);

	v3 = v1 ^ v2;

	memcpy(&out, &v3, 4);

	return out;
}

/**
 * Xor two doubles together.
 *   @left: The left double.
 *   @right: The right double.
 *   &returns: The xored version.
 */
static inline double xor_f64(double left, double right)
{
	double r;

	asm volatile("vxorpd %1,%2,%0" : "=x"(r) : "x"(left), "x"(right));

	return r;

	double out;
	uint64_t v1, v2, v3;

	memcpy(&v1, &left, 8);
	memcpy(&v2, &right, 8);

	v3 = v1 ^ v2;

	memcpy(&out, &v3, 8);

	return out;
}


//typedef uint32_t (*bench_f)(void);

void *BENCH[2][5] = {
	{ base_f32, add_f32, mul_f32, div_f32, NULL },
	{ base_f64, add_f64, mul_f64, div_f64, NULL },
};
