	.intel_syntax noprefix

	.text
	.global mul_dbl

mul_dbl:
	cpuid
	rdtsc
	mov	edi,eax

	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1
	vmulsd	xmm1,xmm0,xmm1

	rdtscp
	mov	esi,eax
	cpuid

	movsd   xmm0,xmm1
	mov	eax,esi
	sub	eax,edi
	ret
