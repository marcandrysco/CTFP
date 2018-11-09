define double @foo(double %a, double %b) {
blk0:
  %r1 = fadd double %a, %b
  ret double %r1
}
