define double @foo(double %a, double %b) {
blk0:
  %r0 = fadd double 0.1, 0.2
  %r1 = fcmp ogt double %r0, 0.0
  %r2 = bitcast double %r0 to i64
  %r3 = select i1 %r1, i64 18446744073709551615, i64 0
  %r4 = and i64 %r2, %r3
  %r5 = bitcast i64 %r4 to double
  %r6 = fadd double %a, %r5
  ret double %r6
}
