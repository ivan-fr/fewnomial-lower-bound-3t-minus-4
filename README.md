# Improved Fewnomial Lower Bound $\mathcal{S}(3, t) \ge 3t - 4$ (Lean 4.36.0 Certified)

[![CI](https://github.com/ivan-fr/fewnomial-lower-bound-3t-minus-4/actions/workflows/ci.yml/badge.svg)](https://github.com/ivan-fr/fewnomial-lower-bound-3t-minus-4/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24515298.svg)](https://doi.org/10.5281/zenodo.24515298)

Formal **Lean 4.36.0** (`Mathlib4`) proofs, preprint, and independent computational verifiers for:

> **An Improved Lower Bound $\mathcal{S}(3, t) \ge 3t - 4$ for Positive Solutions of Bivariate Trinomial–$t$-nomial Systems and an Explicit Degree-45 Eight-Root Example**  
> Ivan Besevic (2026) — Zenodo Preprint: [10.5281/zenodo.24516292](https://doi.org/10.5281/zenodo.24516292) (all versions: [10.5281/zenodo.24515298](https://doi.org/10.5281/zenodo.24515298))

---

## Main Results

Let $\mathcal{S}(3, t)$ denote the maximum number of isolated strictly positive real solutions $(x, y) \in \mathbb{R}_{>0}^2$ of a real bivariate polynomial system $f(x, y) = g(x, y) = 0$ where $f$ is a trinomial (3 monomials) and $g$ is a $t$-nomial ($t \ge 3$ monomials).

| $t$ | System Type | Gomez–Niles–Rojas (2007) | **This work ($3t - 4$)** | El Hilany–Tavenas (2024) |
|---:|:---:|:---:|:---:|:---:|
| $3$ | $(3, 3)$ | $5$ (Haas 2002, sharp) | **5** (sharp) | $5$ |
| $4$ | $(3, 4)$ | $7$ | **8** (+1) | $11$ |
| $5$ | $(3, 5)$ | $9$ | **11** (+2) | $23$ |
| $6$ | $(3, 6)$ | $11$ | **14** (+3) | $47$ |
| $t$ | $(3, t)$ | $2t - 1$ | **$3t - 4$ (+50% slope)** | $\min(3 \cdot 2^{t-2} - 1,\; \frac{2}{3}t^3 + 5t)$ |

### 1. Infinite Lower-Bound Theorem (Lean 4.36.0 Certified)
For every integer $t \ge 3$, there exist bivariate integer polynomials $f, g \in \mathbb{Z}[x, y]$ of exact type $(3, t)$ (nonzero integer coefficients, pairwise distinct monomials) having at least **$3t - 4$ distinct, strictly positive, nondegenerate ($\det J \neq 0$) solutions** in $(0, \infty)^2$.

Formalized via an elementary **Sard-free** constructive induction in [`lean/Fewnomial/InfiniteTheorem.lean`](lean/Fewnomial/InfiniteTheorem.lean) (`2,125` lines):
```lean
Fewnomial.InfiniteTheorem.fewnomial_lower_bound_3t_minus_4 :
  ∀ (t : ℕ), 3 ≤ t →
    ∃ f g roots,
      ValidFewnomial 3 f ∧ ValidFewnomial t g ∧
      Function.Injective roots ∧
      ∀ (k : Fin (3 * t - 4)),
        0 < (roots k).1 ∧ 0 < (roots k).2 ∧
        evalPoly f (roots k).1 (roots k).2 = 0 ∧
        evalPoly g (roots k).1 (roots k).2 = 0 ∧
        det J(f, g)(roots k) ≠ 0
```

### 2. Explicit Degree-45 Eight-Root $(3, 4)$ System (Lean 4.36.0 + 3 Independent Pillars)
$$f_1(x, y) = x^8 + y^8 - 1 = 0, \qquad f_2(x, y) = 8 x^{45} + 8 y^{45} + 35 x^3 y^3 - 25 x y = 0.$$
Symmetric, two-digit coefficients, total degree $45$ (less than half Haas's degree-108 $5$-root trinomial system), with **exact 8 simple strictly positive real solutions**.
- Formalized in [`lean/Fewnomial/Deg45.lean`](lean/Fewnomial/Deg45.lean) (`262` lines): `Fewnomial.Deg45.explicit_deg45_eight_positive_roots`
- Certified in Rust (`src/main.rs`) via (i) zero-float exact `BigInt` interval IVT proof (`0.000 s`) and (ii) direct 2D [`pandsysroots v0.33.0`](https://crates.io/crates/pandsysroots) certification of all `360/360` complex roots (`0.08 s`, exact `8` positive disjoint balls).
- Verified to 200 decimal digits in Python (`verify_records.py`), alongside explicit integer records for $(3, 5)$ (`11` roots) and $(3, 6)$ (`14` roots).

---

## Axiom Audit (Zero `sorry`, Standard Axioms Only)

Every push runs [`lean/Fewnomial/Audit.lean`](lean/Fewnomial/Audit.lean) in GitHub Actions and verifies:
```text
'Fewnomial.Deg45.explicit_deg45_eight_positive_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fewnomial.InfiniteTheorem.fewnomial_lower_bound_3t_minus_4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Reproducing Locally

### Lean 4.36.0 Formal Proofs
```bash
cd lean
lake exe cache get
lake build Fewnomial
lake env lean Fewnomial/Audit.lean
```

### Computational Verifiers (< 1 second)
```bash
cargo run --release       # Pillars 1 & 2: exact BigInt IVT + pandsysroots v0.33.0
python3 verify_records.py # Pillar 3: 200-digit mpmath verification (t = 4, 5, 6)
```

---

## Repository Layout

- [`lean/`](lean/) — Complete Lean 4.36.0 (`Mathlib4`) formalization (`2,404` lines, zero `sorry`)
- [`paper/`](paper/) — AMS LaTeX source and compiled PDF (`v1.1.0`)
- [`src/main.rs`](src/main.rs) & [`Cargo.toml`](Cargo.toml) — Rust zero-float `BigInt` IVT + `pandsysroots v0.33.0` certifier
- [`verify_records.py`](verify_records.py) — Independent 200-digit `mpmath` verifier for $t = 4, 5, 6$
- [`.github/workflows/ci.yml`](.github/workflows/ci.yml) — Automated CI building Lean 4.36.0, auditing axioms, and running Rust & Python verifiers

## License

MIT License (code, Lean proofs, and verification scripts) / CC-BY-4.0 (preprint).
