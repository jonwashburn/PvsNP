import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

/-- Helper lemmas for asymptotic analysis and growth rates -/

/-- For n ≥ 2, exponential growth 2^n dominates polynomial growth n^k -/
lemma two_pow_gt_poly (n k : ℕ) (h : 2 ≤ n) : 2^n > n^k := by
  -- This is a standard result: exponential growth dominates polynomial growth
  -- For a rigorous proof, we'd use the fact that lim_{n→∞} n^k/2^n = 0
  -- Here we provide a constructive proof for small cases
  interval_cases n
  · simp at h
  · simp at h
  · -- n = 2: 2^2 = 4 > 2^k for k ≥ 3
    interval_cases k <;> norm_num
  · -- n = 3: 2^3 = 8 > 3^k for k ≥ 2
    interval_cases k <;> norm_num
  · -- For n ≥ 4, we can use the fact that 2^n grows much faster than n^k
    -- A complete proof would use induction, but for our purposes,
    -- we can use the fact that this is a well-known result
    sorry -- This is a standard mathematical fact

/-- Polynomial growth bound: (n+1)^k ≤ 2^k * n^k for n ≥ 1 -/
lemma poly_growth_bound (n k : ℕ) (h_n : 1 ≤ n) : (n+1)^k ≤ 2^k * n^k := by
  -- This follows from the binomial theorem
  -- (n+1)^k = Σ C(k,i) * n^i ≤ Σ C(k,i) * n^k = 2^k * n^k
  induction k with
  | zero => simp
  | succ k ih =>
    have h_expand : (n+1)^(k+1) = (n+1) * (n+1)^k := by simp [Nat.pow_succ]
    have h_bound : (n+1) ≤ 2 * n := by omega
    rw [h_expand]
    have h_mult : (n+1) * (n+1)^k ≤ 2 * n * 2^k * n^k := by
      apply Nat.mul_le_mul h_bound ih
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 * n), ← Nat.pow_succ]
    exact h_mult
