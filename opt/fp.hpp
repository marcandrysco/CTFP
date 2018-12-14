#pragma once

/*
 * fp declarations
 */
template<class T> T fp_next(T a);

template<class T> T fp_prev(T a);

template<class T> bool fp_eq(T a, T b);
//template bool fp_eq<double>(double a, double b);

template<class T> bool fp_gte(T a, T b);
//template bool fp_gte<double>(double a, double b);

template<class T> bool fp_lte(T a, T b);
//template bool fp_lte<double>(double a, double b);

template<class T> T fp_min(T a, T b);
//template double fp_min<double>(double a, double b);

template<class T> T fp_max(T a, T b);
//template double fp_max<double>(double a, double b);


template <class T> T fp_lsb(T v) {
	int exp;
	std::frexp(v, &exp);
	return exp - std::numeric_limits<T>::digits;
}

template <class T> T fp_lsb2(T a, T b) {
	if((a < 0.0) && (b >= 0.0))
		return fp_lsb(fp_next(0.0));
	else if((a <= 0.0) && (b > 0.0))
		return fp_lsb(fp_next(0.0));
	else
		return std::min(fp_lsb(a), fp_lsb(b));
}
