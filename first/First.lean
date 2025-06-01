-- This module serves as the root of the `First` library.
-- Import modules here that should be built as part of the library.
import First.Basic

import Mathlib

open Nat BigOperators Real Finset

lemma split_sum (f: ℕ → ℝ ) (n: ℕ) (m : ℕ ) (h : 2 ^ (m+1) ≤ n) (hf : ∀ i ∈ Icc 0 n, f i ≥ 0) :
  ∑ i ∈ Icc 1 n, f i ≥ ∑ k ∈ Icc 0 m, ∑ i ∈ Icc (1 + 2^k) (2^(k+1)), f i := by
 
  sorry
