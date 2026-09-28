\\ Independent check (PARI, F_2[x] arithmetic) that f_1^t is NOT (p, -t/24)-even for given t:
\\ find the smallest N with c_t(N) odd and p || 24N + t. Also report the kzker-style count.
pent2(m, B) = {my(v = vectorsmall(B + 1)); for(j = -ceil(sqrt(B)) - 1, ceil(sqrt(B)) + 1, my(e = m * j * (3*j - 1) / 2); if(e >= 0 && e <= B, v[e + 1] = 1)); v};
tofx(v) = Pol(Vecrev(Mod(Vec(v), 2)));
fpow(t, B) = {my(P = Mod(1, 2) + 0*x, i = 0, s = t); while(s, if(s % 2, P = (P * tofx(pent2(2^i, B))) % x^(B + 1)); s \= 2; i++); P};
firstbad(t, p, B) = {my(P = fpow(t, B)); for(N = 0, B, if(polcoef(P, N) != 0 && (24*N + t) % p == 0 && (24*N + t) % p^2 != 0, return(N))); -1};
