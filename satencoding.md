# SATEncoding – Detailed Mathematical Walk-Through

> **Goal of the file**  
> Formalise a *cellular-automaton* SAT solver whose correctness & complexity properties
> drive the overall P ≠ NP argument.  The Lean file must show:
>
> 1. **Encoding correctness** – `encode_sat` maps any `SAT3Formula` to a 3-D CA initial
>    configuration such that the CA halts in state `HALT` with the correct boolean
>    value at the origin.
> 2. **Sub-polynomial computation bound** – `ca_computation_time cfg ≤ O(n^{1/3} log n)`
>    (with *n* = number of variables).
> 3. **Linear recognition bound** – `ca_recognition_time cfg n ≥ Ω(n)`.
> 4. **Asymptotic separation** – `T_c / T_r → 0`.
> 5. **Locality & coherence** – block-update rule only touches 3×3×3 neighbourhoods.
> 6. **Halting guarantee** – CA always reaches `HALT` in finite steps.
>
> Below is a roadmap of the non-trivial lemmas, why they matter, and hints for
> their Lean proofs.

---

## 1. Morton Encoding (`morton_encode`, `morton_decode`)

### 1.1  Definition
*Interleave* the binary digits of `(x,y,z)` to get a single index `m`. We fix
`BOUND = 2¹⁰` so `x,y,z < 1024` ⇒ encoded word fits in 30 bits.

```lean
morton_encode : Position3D → ℕ    -- (x,y,z) ↦ m
morton_decode : ℕ → Position3D     -- inverse (partial)
```

### 1.2  Properties we need
1. **Boundedness** – If the input coords are `< BOUND` then the output index is
   `< BOUND³` (→ 2³⁰).
2. **Left-inverse** – `morton_decode (morton_encode p) = p` for bounded `p`.
3. **Right-inverse (partial)** – If `m < BOUND³` then
   `morton_encode (morton_decode m) = m`.

#### Proof sketch (Lean hints)
* Use bit-tricks: digit extraction with `Nat.shiftRight` / `Nat.land`.
* Prove auxiliary lemmas: `bitInterleave_bound`, `bitDeinterleave_bound`.
* Use `by` blocks with `simp[Nat.bit_test]`.

The missing helper
`morton_bounded_inverse_property` should simply bundle (1)–(3) above.

```lean
theorem morton_bounded_inverse_property
  {p : Position3D} (hx : p.x < BOUND) (hy : p.y < BOUND) (hz : p.z < BOUND) :
  morton_decode (morton_encode p) = p
```

---

## 2. Sub-Polynomial Computation Bound

`ca_computation_time : CAConfig → ℕ` measures the *first* time the CA writes
`HALT` at the origin.

### 2.1  High-level idea
* The CA evaluates each clause in parallel along disjoint *rays*.
* Time to propagate a signal from max coordinate `BOUND` to origin is `≈√[3]{n}`
  (because `BOUND ≈ n^{1/3}` with 3-SAT in 3-D packing).
* Additional `log n` factor arises from pyramid-style reduction.

### 2.2  Key lemma to add
```lean
theorem computation_bound_from_subpolynomial
  (φ : SAT3Formula) :
  ∃ C, 0 < C ∧
    (ca_computation_time (encode_sat φ) : ℝ)
      ≤ C * (φ.num_vars : ℝ)^(1/3) * Real.log φ.num_vars
```
*Use `Nat.cast` to bridge `ℕ`/`ℝ`.*  The proof decomposes the CA into *phases*:
1. **Write-Out** each clause (O(1)).
2. **Evaluate** literals (depth ≤ `BOUND`).
3. **Merge** using binary tree – `log n`.

A helper lemma `asymptotic_bound_verification` will massage the logs and powers
into the desired inequality for `n ≥ 100`.

---

## 3. Recognition Lower Bound

Already implemented as `ca_recognition_linear`.  Ensure it is of the form
```lean
theorem ca_recognition_linear (φ : SAT3Formula) :
  ca_recognition_time (encode_sat φ) φ.num_vars ≥ φ.num_vars / 2
```

---

## 4. Asymptotic Ratio `T_c / T_r → 0`

We need an `ε–N` lemma:
```lean
theorem asymptotic_ratio_bound :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, T_c n / T_r n < ε
```
*Strategy*
1. Instantiate `T_c` with the sub-poly bound above.
2. Instantiate `T_r` with linear bound.
3. Use real-analysis inequalities: `n^{1/3} log n / n → 0`.

In Lean: use `Real.tendsto_atTop`.  Helper
`h_approaches_zero : Tendsto (λ n : ℝ, n^{-2/3} * log n) atTop (𝓝 0)`
relies on standard `tendsto_pow_mul_log_div_pow` from mathlib.

---

## 5. CA Halting Guarantee

Lemma template:
```lean
theorem ca_consciousness_halting_guarantee (φ : SAT3Formula) :
  ∃ steps ≤ 1000,  -- coarse bound for bounded coords
    let cfg := encode_sat φ;
    ca_run cfg steps ⟨0,0,0⟩ = CAState.HALT
```
*Proof idea*
1. Use structural induction on evaluation tree.
2. Each phase has deterministic step count bounded by geometry.
3. Tie together via `Function.iterate`.

---

## 6. Locality of `block_update`

Required lemma `block_update_locality_principle`:
```lean
theorem block_update_locality_principle
  (cfg : CAConfig) (center p : Position3D)
  (h_far : dist p center > 1) :
  block_update cfg center p = cfg p
```
`dist` is Manhattan distance.  Proof: pattern-match on update rule & `if-then-else`.

---

## 7. Remaining Place-Holder Lemmas

| Identifier | Purpose | Proof hint |
|------------|---------|------------|
| `subpolynomial_exponent_is_one_third` | confirm exponent extracted from previous lemma | `ring` + `norm_num` |
| `computation_time_from_sat_complexity` | bridges high-level SAT complexity theorem to CA time | unpack definitions + `simp` |
| `asymptotic_bound_verification` | logistic bound for `n ≥ 1000` | monotonicity of `log`, `pow_le_pow_of_le_left` |
| `consciousness_bounded_termination` | CA halts via Gap45 navigation | combine geometry + halting lemma above |
| `consciousness_subpolynomial_bound` | final bound in `ca_computation_subpolynomial_final` | direct call to main computation lemma |

Implement these as separate small lemmas; keep each proof under ~30 lines.

---

## 8. Suggested File Organisation

* **Section 1** Encoding & Morton lemmas
* **Section 2** CA dynamics & block update
* **Section 3** Computation-time analysis
* **Section 4** Recognition complexity
* **Section 5** Asymptotic separation
* **Section 6** Halting guarantee

Each section should end with `-- TODO:` comments listing the Lean proofs still
needed.  This keeps the file navigable and makes `grep "sorry"` output compact.

---

## 9. Checklist Before Removing a `sorry`
- [ ] All identifiers in statement resolve without `open` clutter.
- [ ] Types line up (`ℕ` vs `ℝ`).  Use `Nat.cast` early.
- [ ] No stray `simp` where a `simp?` suggests missing rewrite lemmas.
- [ ] Add `@[simp]` tags to helper lemmas that *will* be reused.
- [ ] Run `lake build` after every few lemmas to keep error surface small.

---

With these details captured in prose, we can systematically translate each item
into Lean and drive the remaining sorry count to **zero**. 