import Fewnomial

/-!
# Independent Axiom Audit for `Fewnomial`
Run with: `lake env lean Fewnomial/Audit.lean`
Confirms that both main theorems depend ONLY on standard Lean 4 axioms
(`propext`, `Classical.choice`, `Quot.sound`) — ZERO `sorryAx`, ZERO custom axioms,
ZERO `Lean.ofReduceBool`.
-/

#check @Fewnomial.Deg45.explicit_deg45_eight_positive_roots
#print axioms Fewnomial.Deg45.explicit_deg45_eight_positive_roots

#check @Fewnomial.InfiniteTheorem.fewnomial_lower_bound_3t_minus_4
#print axioms Fewnomial.InfiniteTheorem.fewnomial_lower_bound_3t_minus_4
