#ifndef IVALI64_HPP
#define IVALI64_HPP

/*
 * 64-bit integer class
 */
class IvalI64 {
public:
	uint64_t lo, hi;

	IvalI64(uint64_t _lo, uint64_t _hi) { lo = _lo; hi = _hi; };
	~IvalI64() { }

	static IvalI64 All() { return IvalI64(0, UINT64_MAX); }
	static IvalI64 Const(uint64_t val) { return IvalI64(val, val); }
};

#endif
