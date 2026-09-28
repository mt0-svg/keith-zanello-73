\\ Check of the t = 5 argument (the proposition on t = 5 in the paper).
\\ (a) c_5(N) = (1/2) sum_{d | 24N+5} chi_{-4}(d) mod 2, for N < L (f_1^5 computed exactly over Z).
\\ (b) (p, -5/24)-evenness for the primes p = 1 mod 24 up to 1009 on N < L, and failure for p = 5 mod 24 up to 173.
default(parisizemax, "2G");
L = 200000;
f = Vec(eta('q + O('q^L))^5);
bad = 0;
for (N = 0, L - 1, m = 24*N + 5; s = sumdiv(m, d, kronecker(-4, d)); if ((f[N+1] - s/2) % 2, bad++));
print("(a) mismatches of the divisor formula for N < ", L, ": ", bad);
ev(p) = {my(r = lift(Mod(-5, p^2)/24), c = 0); for (N = 0, L - 1, if (N % p == r % p && N % p^2 != r && f[N+1] % 2, c++)); c};
print("(b) odd coefficients in the progressions of base -5/24, p = 1 mod 24: ", vector(#select(p -> p % 24 == 1, primes(170)), i, my(P = select(p -> p % 24 == 1, primes(170))[i]); [P, ev(P)]));
print("    control, p = 5 mod 24: ", apply(p -> [p, ev(p)], select(p -> p % 24 == 5, primes(40))));
