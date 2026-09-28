\\ Closed forms used by the Lean formalization of the level 9 step (KZ73/Modular/Arith.lean):
\\   (a) F2 = (H0 - H0p - 9 G)/54 equals (1/3) sum_{n == 2 mod 3} s1(n) q^n,
\\       and 3 | s1(n) for n == 2 (mod 3);
\\   (b) -(E2(z) - 4 E2(3z) + 3 E2(9z))/24 = sum_{3 not | n} s1(n) q^n;
\\   (c) G = (1/(24 i sqrt 3)) sum_{u mod 3} chi(u) (1 - E2(z + u/3)) coefficientwise,
\\       i.e. sum_u chi(u) e^{2 pi i n u/3} = chi(n) * i sqrt(3)  (Gauss sum).
\\ Run: gp -q level9_f2.gp < /dev/null      (verdict: last line RESULT PASS / FAIL)
default(parisizemax, 500000000);
default(nbthreads, 1);
NB = 5000;
s1(n) = if(denominator(n) != 1 || n < 1, 0, sigma(n));
chi(n) = kronecker(-3, n);
coefH0(n)  = if(n == 0, 1, 12*(s1(n) - 3*s1(n/3)));
coefH0p(n) = if(n == 0, 1, 3*(s1(n) - 9*s1(n/9)));
coefG(n)   = if(n == 0, 0, chi(n)*s1(n));
coefE2(m) = if(denominator(m) != 1, 0, if(m == 0, 1, -24*s1(m)));
main() =
{
  my(ok = 1, bad, w = exp(2*Pi*I/3), g);
  bad = 0;
  for(n = 0, NB,
    my(f2 = (coefH0(n) - coefH0p(n) - 9*coefG(n))/54, cf = if(n % 3 == 2, s1(n)/3, 0));
    if(f2 != cf || denominator(cf) != 1, bad++));
  print("(a) F2 coefficient = s1(n)/3 [n == 2 mod 3], integral, up to n = ", NB, ": mismatches ", bad);
  if(bad, ok = 0);
  bad = 0;
  for(n = 0, NB,
    my(l = -(coefE2(n) - 4*coefE2(n/3) + 3*coefE2(n/9))/24,
       r = if(n % 3 == 0, 0, s1(n)));
    if(l != r, bad++));
  print("(b) -(E2(z) - 4E2(3z) + 3E2(9z))/24 = sum_{3 not | n} s1(n) q^n up to n = ", NB, ": mismatches ", bad);
  if(bad, ok = 0);
  g = sum(u = 0, 2, chi(u) * w^u);
  bad = 0;
  for(n = 0, 60, if(abs(sum(u = 0, 2, chi(u) * w^(n*u)) - chi(n) * g) > 1e-30, bad++));
  print("(c) Gauss sum g = ", g, " (i sqrt 3 = ", I*sqrt(3), "); sum_u chi(u) w^(nu) = chi(n) g for n <= 60: mismatches ", bad);
  if(bad || abs(g - I*sqrt(3)) > 1e-30, ok = 0);
  print(if(ok, "RESULT PASS", "RESULT FAIL"));
}
main();
