\\ The character rho of eta^8 (eta(gamma z)^8 = rho(gamma) (cz+d)^4 eta(z)^8, rho(S) = 1, rho(T) = e^{2 pi i/3})
\\ factors through SL_2(Z/3): rho = e^{2 pi i psi/3} with psi(gamma) = (a+d)c - bd(c^2-1) mod 3.
\\ Check: the hom SL_2(F_3) -> Z/3 with S -> 0, T -> 1 (built by BFS over words in S, T) equals psi.
\\ Run: gp -q eta8_character.gp < /dev/null
fpsi(M) = lift((M[1,1] + M[2,2])*M[2,1] - M[1,2]*M[2,2]*(M[2,1]^2 - 1));
main() =
{
  my(S = Mod([0,-1;1,0],3), T = Mod([1,1;0,1],3), I2 = Mod(matid(2),3), V = Map(), Q = List([[I2, 0]]), bad = 0, n = 1);
  mapput(V, [1,0,0,1], 0);
  while(#Q, my(x = Q[1]); listpop(Q, 1);
    foreach([[S, 0], [T, 1]], g,
      my(M = x[1]*g[1], v = (x[2] + g[2]) % 3, k = [lift(M[1,1]), lift(M[1,2]), lift(M[2,1]), lift(M[2,2])], w);
      if(!mapisdefined(V, k, &w), mapput(V, k, v); listput(Q, [M, v]); n++; if(fpsi(M) != v, bad++))));
  print("elements checked: ", n, "; mismatches with (a+d)c - bd(c^2-1) mod 3: ", bad);
}
main();
quit;
