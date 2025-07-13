# Asymptotic Analysis Notes

Extracted from `Src/PvsNP/AsymptoticAnalysis.lean` to separate code and prose.

## BoundCAExpansion
The CA halts or cycles within O(n^{1/3} log n) steps due to lattice diameter O(n^{1/3}) and tree depth log n. For cycles, use pigeonhole on finite states to find minimal k, bound by active region.

## floor_computation_bound_strict
Proves n^{1/3} log n < n/2 for n ≥ 10 via case analysis: moderate n with direct bounds, large n with o(n) asymptotics, and induction on small n with derivative <1 increment.

(Include @jonwashburn for attribution) 