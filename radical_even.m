/*
  Proof of concept for the root choice for even N ("Getting to the right root", Section 4).

  For p = 7 mod 8, curves on the surface of the 2-isogeny volcano, and random points P of even
  order N spanning a horizontal kernel, we compute one radical N-step for both rational roots
  +-beta of rho_N and compare with Velu's formulae. We check:
    (a) Theorem 3.1: the radical step gives the Velu codomain, and (r,t) lies on it;
    (b) Theorem 4.1: beta*theta is a square, with theta = -x(T_3) on E_{b',c'};
    (c) Corollary 4.10: exactly one root keeps the next step horizontal, namely the square root
        beta_0 = rho_N^((p+1)/(2N)) if P is halvable over F_p, and -beta_0 otherwise.
  Horizontality is tested via Velu: a cyclic kernel is horizontal iff its codomain is again on the
  surface, i.e. has full rational 2-torsion. This is a correctness check only.
*/

// ---------------------------------------------------------------- parameters

r := 7;                                           // ord_2(p+1)
f := 1;
while not IsPrime(2^r*15*f - 1) do f +:= 2; end while;
p  := 2^r*15*f - 1;                               // p = 7 mod 8, and 3, 5 divide p+1
F  := GF(p);
Ns := [4, 6, 8, 10, 12, 16, 24, 32, 64, 96, 192];  // all with N | (p+1)/2


// ---------------------------------------------------------------- helpers

// x-coordinates of the 2-torsion points are the roots of 4x^3 + b2 x^2 + 2 b4 x + b6.
TwoTorsion := function(E)
  a1, a2, a3 := Explode(aInvariants(E));
  b2, b4, b6 := Explode(bInvariants(E));
  R<X> := PolynomialRing(F);
  return [E | [x, -(a1*x + a3)/2] : x in [rt[1] : rt in Roots(4*X^3 + b2*X^2 + 2*b4*X + b6)]];
end function;

OnSurface := func< E | #TwoTorsion(E) eq 3 >;
Halvable  := func< Q | #DivisionPoints(Q, 2) gt 0 >;

// Velu codomain for the kernel <P> of order N (Section 2.4).
VeluCodomain := function(E, P, N)
  a1, a2, a3, a4, a6 := Explode(aInvariants(E));
  b2 := a1^2 + 4*a2;
  v := F!0; w := F!0;
  for k in [1..N div 2] do                        // one point of each pair {Q,-Q}, and [N/2]P once
    Q := k*P; x := Q[1]; y := Q[2];
    gx := 3*x^2 + 2*a2*x + a4 - a1*y;
    gy := -2*y - a1*x - a3;
    vQ := (2*k eq N) select gx else 2*gx - a1*gy;
    v +:= vQ;  w +:= gy^2 + x*vQ;
  end for;
  return EllipticCurve([a1, a2, a3, a4 - 5*v, a6 - b2*v - 7*w]);
end function;

// Image of R (not in <P>) under the Velu isogeny with kernel <P>.
VeluImage := function(E, P, N, R, E1)
  X := R[1]; Y := R[2];
  for k in [1..N-1] do
    Q := k*P; S := R + Q;
    X +:= S[1] - Q[1];  Y +:= S[2] - Q[2];
  end for;
  return E1![X, Y];
end function;

// Tate normal form (b, c) of (E, P) (Lemma 2.2).
Tate := function(E, P)
  a1, a2, a3, a4, a6 := Explode(aInvariants(E));
  x0 := P[1]; y0 := P[2];
  psi2 := 2*y0 + a1*x0 + a3;
  lam  := (3*x0^2 + 2*a2*x0 + a4 - a1*y0)/psi2;
  x2   := lam^2 + a1*lam - a2 - 2*x0;
  u    := psi2/(x0 - x2);
  return (x2 - x0)/u^2, 1 - (a1 + 2*lam)/u;
end function;


// ---------------------------------------------------------------- the radical step

// One radical N-step on E_{b,c} for a given N-th root beta of rho_N (Theorem 3.1 via Proposition 3.2).
// Returns the isomorphism (u, r, s, t) and (b', c').
Step := function(b, c, N, beta)
  E  := EllipticCurve([F| 1-c, -b, -b, 0, 0]);
  P0 := E![0, 0];
  x  := [F| (k*P0)[1] : k in [1..N-2]];
  al := -beta;  ial := 1/al;  n := N - 2;
  h  := [al];
  for i in [2..n] do Append(~h, h[i-1]*al*x[i]); end for;

  S1  := b*&+h;
  S11 := b^2*&+[F| e^2 : e in h];
  S2  := b*ial*&+[F| h[i]*h[i+1] : i in [1..n-1]] - b*h[n];
  S3  := ial^3*&+[F| h[i]*h[i+1]*h[i+2] : i in [1..n-2]] - h[n]^2*ial^2 - h[n]*ial;
  S12 := b^2*ial*&+[F| h[i]^2*h[i+1] : i in [1..n-1]];

  u := 1 + 3*S1 - S3;
  s := 2*S1 - S2;
  r := (S1 + S2)*(1 - S3) + (F!3/2)*(S1^2 - S11) - S12;
  t := (u*(3*r - b - (1-c)*s - s^2) + b - (1-c)*r)/2;
  return u, r, s, t, (b + (1-c)*s + s^2 - 3*r)/u^2, 1 - (1-c+2*s)/u;
end function;


// ---------------------------------------------------------------- test

SetSeed(1);
E0 := EllipticCurve([F| -1, 0]);                  // y^2 = x^3 - x lies on the surface
assert OnSurface(E0);
e  := (p+1) div 2;                                // exponent of E(F_p) on the surface

for N in Ns do
  tested := 0; ok := true; types := {};
  while tested lt 4 do
    // a random point of exact order N spanning a horizontal kernel
    A := (e div N)*Random(E0);
    P := Random([A + S : S in [E0!0] cat TwoTorsion(E0)]);
    if Order(P) ne N or not OnSurface(VeluCodomain(E0, P, N)) then continue; end if;
    tested +:= 1;

    b, c := Tate(E0, P);
    E  := EllipticCurve([F| 1-c, -b, -b, 0, 0]);
    P0 := E![0, 0];
    Include(~types, Halvable(P0));

    // the radical (Lemma 3.4) and its two rational roots
    rho   := (-1)^(N+1)/(b^2*&*[F| (k*P0)[1] : k in [2..N-2]]);
    beta0 := rho^((p+1) div (2*N));
    ok := ok and (beta0^N eq rho and IsSquare(beta0));

    // Velu codomain and the point T of order 2 in ker(phi^), as the image of S in E[2] outside <P0>
    E1 := VeluCodomain(E, P0, N);
    S  := [Q : Q in TwoTorsion(E) | Q ne (N div 2)*P0][1];
    T  := VeluImage(E, P0, N, S, E1);

    horizontal := [];
    for beta in [beta0, -beta0] do
      u, r, s, t, b1, c1 := Step(b, c, N, beta);
      E2 := EllipticCurve([F| 1-c1, -b1, -b1, 0, 0]);
      ok := ok and (jInvariant(E2) eq jInvariant(E1) and IsPoint(E1, [r, t]));   // (a)

      Ts    := E2![(T[1] - r)/u^2, (T[2] - s*(T[1] - r) - t)/u^3];          // iota^{-1}(T)
      theta := -((N div 2)*E2![0, 0] + Ts)[1];
      ok := ok and IsSquare(beta*theta);                                     // (b)

      Append(~horizontal, OnSurface(VeluCodomain(E2, E2![0, 0], N)));
    end for;
    ok := ok and horizontal eq [Halvable(P0), not Halvable(P0)];             // (c)
  end while;
  printf "N = %3o: halvable cases seen %o, all checks %o\n", N, types, ok;
end for;
