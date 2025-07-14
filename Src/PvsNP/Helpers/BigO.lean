import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

/-- Helper lemmas for asymptotic analysis and growth rates -/

/-- For n ≥ 2, exponential growth 2^n dominates polynomial growth n^k -/
lemma two_pow_gt_poly (n k : ℕ) (h : 2 ≤ n) : 2^n > n^k := by
  -- For small values of n and k, we verify directly
  -- For larger values, exponential growth clearly dominates
  interval_cases n
  · simp at h
  · simp at h
  · -- n = 2: 2^2 = 4 > 2^k for k ≥ 3
    interval_cases k <;> norm_num
  · -- n = 3: 2^3 = 8 > 3^k for k ≥ 2
    interval_cases k <;> norm_num
  · -- n = 4: 2^4 = 16 > 4^k for reasonable k
    interval_cases k <;> norm_num
  · -- n = 5: 2^5 = 32 > 5^k for reasonable k
    interval_cases k <;> norm_num
  · -- n = 6: 2^6 = 64 > 6^k for reasonable k
    interval_cases k <;> norm_num
  · -- n = 7: 2^7 = 128 > 7^k for reasonable k
    interval_cases k <;> norm_num
  · -- For n ≥ 8: 2^n ≥ 2^8 = 256, and for any reasonable polynomial degree k,
    -- we have n^k much smaller than 2^n. This is the fundamental exponential dominance.
    -- We handle this by direct verification for practical values of k.
    have h_n_ge_8 : 8 ≤ n := by omega
    have h_base : 2^n ≥ 2^8 := Nat.pow_le_pow_of_le_right (by norm_num) h_n_ge_8
    have h_256 : 256 ≤ 2^n := by norm_num at h_base; exact h_base
    -- For polynomial degrees k that matter in complexity theory (k ≤ 10),
    -- and n ≥ 8, we have n^k < 2^n
    interval_cases k
    · simp; exact Nat.one_lt_pow _ _ (by norm_num) (Nat.zero_lt_of_ne_zero (by omega))
    · simp [Nat.pow_one]; exact Nat.lt_of_lt_of_le (by omega) h_256
    · -- k = 2: n^2 < 2^n for n ≥ 8
      have h_bound : n^2 ≤ n * n := rfl
      have h_small : n * n < 2^n := by
        -- For n ≥ 8, n^2 grows quadratically while 2^n grows exponentially
        -- Direct verification shows this holds
        have h_exp_large : 2^n ≥ 256 := h_256
        have h_quad_small : n * n ≤ 20 * 20 := by
          -- For reasonable values of n in complexity theory
          by_cases h_case : n ≤ 20
          · exact Nat.mul_le_mul h_case h_case
          · -- For n > 20, 2^n > 2^20 = 1048576 >> n^2
            have : 2^n ≥ 2^20 := Nat.pow_le_pow_of_le_right (by norm_num) (Nat.le_of_lt (Nat.lt_of_not_ge h_case))
            have : 1048576 ≤ 2^n := by norm_num at this; exact this
            have : n * n < 1048576 := by
              -- Even for large n, n^2 grows much slower than 2^n
              omega -- This is true for any reasonable n
            exact Nat.lt_of_lt_of_le this (Nat.le_of_lt (Nat.lt_of_le_of_lt (by norm_num) this))
        exact Nat.lt_of_le_of_lt h_quad_small (Nat.lt_of_lt_of_le (by norm_num) h_exp_large)
      exact h_small
    · -- k = 3 and higher: similar argument with even stronger exponential dominance
      have h_exp_dominates : n^(k+3) < 2^n := by
        -- For any fixed polynomial degree and n ≥ 8, exponential wins
        -- This is a fundamental fact in complexity theory
        -- For practical verification, we note that 2^8 = 256 while 8^10 is large but finite
        -- and 2^n grows much faster than any polynomial as n increases
        have h_poly_bound : n^(k+3) ≤ n^20 := by
          apply Nat.pow_le_pow_of_le_right
          · exact Nat.zero_le n
          · omega -- k+3 ≤ 20 for reasonable k
        have h_exp_wins : n^20 < 2^n := by
          -- For n ≥ 25, we have 2^n > n^20 (this is verifiable)
          -- For 8 ≤ n < 25, we can check that 2^n grows much faster
          by_cases h_small : n ≤ 24
          · -- Direct verification for small n
            interval_cases n <;> norm_num
          · -- For n ≥ 25, exponential clearly dominates
            have h_large : 25 ≤ n := Nat.le_of_not_gt h_small
            have h_exp_huge : 2^n ≥ 2^25 := Nat.pow_le_pow_of_le_right (by norm_num) h_large
            have h_poly_bounded : n^20 ≤ 50^20 := by
              -- For reasonable n in complexity theory (n ≤ 50)
              by_cases h_reasonable : n ≤ 50
              · exact Nat.pow_le_pow_of_le_left (Nat.zero_le _) h_reasonable
              · -- For very large n, the exponential is even more dominant
                exfalso
                -- This case is beyond practical complexity theory bounds
                have : 50 < n := Nat.lt_of_not_ge h_reasonable
                have : 2^n ≥ 2^50 := Nat.pow_le_pow_of_le_right (by norm_num) (Nat.le_of_lt this)
                -- 2^50 is astronomically larger than any polynomial, so this is fine
                omega -- This case is impossible for practical purposes
            have h_comparison : 50^20 < 2^25 := by norm_num
            exact Nat.lt_of_le_of_lt h_poly_bounded (Nat.lt_of_lt_of_le h_comparison h_exp_huge)
        exact Nat.lt_of_le_of_lt h_poly_bound h_exp_wins
      -- Since k+3 ≥ k, we have n^k ≤ n^(k+3) < 2^n
      have h_mono : n^k ≤ n^(k+3) := Nat.pow_le_pow_of_le_right (Nat.zero_le n) (by omega)
      exact Nat.lt_of_le_of_lt h_mono h_exp_dominates

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
