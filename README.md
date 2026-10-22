# Getting to the right root: radical isogenies of every degree

Magma scripts accompanying the paper. They are proofs of concept for correctness only: no attempt is made at efficiency or constant-time behaviour.

## `radical_main.m`

Evaluates the class group action of `prod_l (l, pi - 1)^{e_l}` on supersingular curves over the toy prime `p = 4 f prod_{3 <= l <= 97} l - 1` in two ways:

- with Vélu's formulae and sampled kernel points;
- with the inversion-free radical steps of Algorithm 5.2, starting each chain from the x-only Tate normal form of Proposition 5.5 (Vélu is still used for `l = 3`).

Negative exponents are handled via the quadratic twist. For five random keys with exponents in `{-3, ..., 3}` and for the maximal key, the script checks that both methods give `F_p`-isomorphic curves, and that applying the inverse key leads back to the starting curve.

## `radical_even.m`

Tests the root choice for even `N` (Section 4). It works over `p = 2^7 * 15 * f - 1` (so `p = 7 mod 8`), starting from `y^2 = x^3 - x` on the surface of the 2-isogeny volcano, with `N in {4, 6, 8, 10, 12, 16, 24, 32, 64, 96, 192}` and random points `P` of order `N` spanning horizontal kernels, both halvable and non-halvable. For both rational roots `±beta_0` of the radical, it checks that

1. the radical step gives the Vélu codomain, and `(r, t)` lies on it (Theorem 3.1);
2. `beta * theta` is a square (Theorem 4.1);
3. exactly one root keeps the next step horizontal, namely `beta_0 = rho_N^((p+1)/(2N))` if `P` is halvable over `F_p`, and `-beta_0` otherwise (Corollary 4.10).

## Usage

```
magma radical_main.m
magma radical_even.m
```

Each script prints one line per test case, reporting whether all checks passed.
