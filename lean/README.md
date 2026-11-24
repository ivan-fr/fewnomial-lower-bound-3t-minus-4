# Lean 4.36.0 Formal Certification of $\mathcal{S}(3, t) \ge 3t - 4$

This directory contains the complete, self-contained **Lean 4.36.0** (`Mathlib4`) machine verification of both main theorems from *An Improved Lower Bound $\mathcal{S}(3, t) \ge 3t - 4$ for Positive Solutions of Bivariate Trinomial--$t$-nomial Systems and an Explicit Degree-45 Eight-Root Example* (Ivan Besevic, 2026).

## Certified Theorems

1. **`Fewnomial.InfiniteTheorem.fewnomial_lower_bound_3t_minus_4`** ([Fewnomial/InfiniteTheorem.lean](Fewnomial/InfiniteTheorem.lean), 2,125 lines):
   For every integer $t \ge 3$, proves the existence of valid bivariate integer polynomials $f, g \in \mathbb{Z}[x, y]$ (`ValidFewnomial 3 f` and `ValidFewnomial t g` — exact term counts, nonzero integer coefficients, pairwise distinct exponent pairs) admitting `3 * t - 4` distinct, strictly positive, **nondegenerate** ($\det J(x_k, y_k) \neq 0$) solutions in $(0, \infty)^2$, via an elementary Sard-free constructive induction.
2. **`Fewnomial.Deg45.explicit_deg45_eight_positive_roots`** ([Fewnomial/Deg45.lean](Fewnomial/Deg45.lean), 262 lines):
   Certifies that the explicit degree-45 symmetric system $x^8 + y^8 - 1 = 0$, $8 x^{45} + 8 y^{45} + 35 x^3 y^3 - 25 x y = 0$ has 8 distinct strictly positive solutions in $(0, \infty)^2$.

## Verification & Axiom Audit

Requires `elan` / Lean `v4.36.0` (automatically selected by `lean-toolchain`). To fetch prebuilt Mathlib oleans and verify both theorems and their exact axiom dependencies:

```bash
lake exe cache get
lake build Fewnomial
lake env lean Fewnomial/Audit.lean
```

Expected audit output:
```text
'Fewnomial.Deg45.explicit_deg45_eight_positive_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fewnomial.InfiniteTheorem.fewnomial_lower_bound_3t_minus_4' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`.
