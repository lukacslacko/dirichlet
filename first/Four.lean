-- This module serves as the root of the `Four` library.
-- Import modules here that should be built as part of the library.

import Mathlib

open Nat Finset BigOperators Set Real

def r1 : Real := 1
def r2 : Real := 2
def r4 : Real := 4

lemma sum_le_log (k : Nat) : ∑ i ∈ range (2 ^ k), r1 / (i + 1) ≤ (k + 1) := by
  unfold r1
  induction k
  case zero => simp
  case succ k hk =>
    set a := range (2 ^ k)
    set b := range (2 ^ (k + 1))
    set c := b \ a

    have a_sub_b : a ⊆ b := Finset.range_subset.mpr (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))

    rw [← Finset.sdiff_union_of_subset a_sub_b, Finset.sum_union (disjoint_sdiff.symm), add_comm]

    apply _root_.add_le_add

    exact_mod_cast hk

    have h_lower : ∀ i ∈ c, i ≥ 2 ^ k := fun i hi =>
      Nat.not_lt.mp (fun h => (Finset.mem_sdiff.mp hi).right (Finset.mem_range.mpr h))

    have h_card : #c = 2 ^ k := by
      rw [Finset.card_sdiff a_sub_b, Finset.card_range, Finset.card_range, pow_succ, mul_two]
      simp

    calc
      ∑ x ∈ b \ a, r1 / (x + 1) = ∑ x ∈ c, r1 / (x + 1) := by rfl
      _ ≤ ∑ x ∈ c, 1 / (2 ^ k) := by
        apply Finset.sum_le_sum
        intro i hi
        apply le_of_one_div_le_one_div
        simp
        unfold r1
        field_simp
        exact_mod_cast le_succ_of_le (h_lower i hi)
      _ = #c • (1 / (2 ^ k)) := by rw [Finset.sum_const]
      _ = 1 := by rw [h_card]; field_simp

lemma half_log_le_sum (k : Nat) : (k + 1) / r2 ≤ ∑ i ∈ range (2 ^ k), r1 / (i + 1) := by
  unfold r1 r2
  induction k
  case zero => norm_num
  case succ k hk =>
    set a := range (2 ^ k)
    set b := range (2 ^ (k + 1))
    set c := b \ a

    have a_sub_b : a ⊆ b := Finset.range_subset.mpr (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))

    rw [← Finset.sdiff_union_of_subset a_sub_b, Finset.sum_union (disjoint_sdiff.symm), add_comm]

    rw [add_div]
    apply _root_.add_le_add
    swap
    exact_mod_cast hk

    have h_upper : ∀ i ∈ c, i < 2 ^ (k + 1) := by
      intro i hi
      apply Finset.mem_sdiff.mp at hi
      apply Finset.mem_range.mp hi.left

    have h_card : #c = 2 ^ k := by
      rw [Finset.card_sdiff a_sub_b, Finset.card_range, Finset.card_range, pow_succ, mul_two]
      simp

    have h_recip_lower: ∀ i ∈ c, r1 / (i + 1) ≥ r1 / (2 ^ (k + 1)) := by
      intro i hi
      apply le_of_one_div_le_one_div
      unfold r1
      simp
      exact_mod_cast Nat.zero_lt_succ i
      unfold r1
      field_simp
      have : i + 1 ≤ 2 ^ (k + 1) := by
        exact h_upper i hi
      exact_mod_cast this

    calc
      ∑ i ∈ c, r1 / (i + 1)
      ≥ ∑ i ∈ c, r1 / (2 ^ (k + 1)) := by
        apply Finset.sum_le_sum h_recip_lower
      _ = #c • (r1 / (2 ^ (k + 1))) := by
        rw [Finset.sum_const]
      _ = (2 ^ k) • (r1 / (2 ^ (k + 1))) := by
        rw [h_card]
      _ = (2 ^ k) * (r1 / (2 ^ (k + 1))) := by
        unfold r1
        simp
      _ = 2 ^ k / (2 ^ (k + 1)) := by
        unfold r1
        ring
      _ = 2 ^ k / (2 ^ k * 2) := by
        rw [pow_succ]
      _ = r1 / 2 := by
        unfold r1
        field_simp

theorem sum_between_log (k : Nat) :
  (k + 1) / r2 ≤ ∑ i ∈ range (2 ^ k), r1 / (i + 1) ∧
  ∑ i ∈ range (2 ^ k), r1 / (i + 1) ≤ (k + 1) := by
  constructor
  exact half_log_le_sum k
  exact sum_le_log k

theorem sum_square_lt_two (k : Nat) :
  ∑ i ∈ range k, (r1 / (i + 1) ^ 2) < r2 := by
    cases k
    case zero =>
      unfold r1 r2
      norm_num
    case succ k =>
    set f1 := fun (i : Nat) => r1 / (i + 1) ^ 2
    set f2 := fun (i : Nat) => r1 / (i * (i + 1))
    set f3 := fun (i : Nat) => r1 / (i + 1)
    have f1_le_f2 (i : Nat) (hi : i > 0) : f1 i ≤ f2 i := by
      unfold f1 f2 r1
      gcongr
      nlinarith
    have f2_eq_f3 (i : Nat) : f2 (i + 1) = f3 i - f3 (i + 1) := by
      unfold f2 f3 r1
      field_simp
    unfold r2

    rw [Finset.sum_range_succ']
    unfold r1
    field_simp
    have : ∑ i ∈ range k, f1 (i + 1) < 1 := by
      calc
        ∑ i ∈ range k, f1 (i + 1) ≤ ∑ i ∈ range k, f2 (i + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          apply f1_le_f2
          linarith
        _ = ∑ i ∈ range k, (f3 i - f3 (i + 1)) := by
          apply Finset.sum_congr
          rfl
          intro i hi
          apply f2_eq_f3
        _ = f3 0 - f3 k := by
          apply sum_range_sub'
      unfold f3 r1
      field_simp
      refine (div_lt_one ?_).mpr ?_
      linarith
      simp
    unfold f1 r1 at this
    norm_num at this
    simp
    linarith

  def primes (n : Nat) : Finset Nat :=
    (Finset.range n).filter (fun i => Nat.Prime i)

lemma smallest_prime {n : Nat} (p : Nat) (hp : p ∈ primes n) :
  2 ≤ p := by
  contrapose! hp
  cases p
  case zero =>
    unfold primes
    simp
    norm_num
  case succ p =>
    cases p
    case zero =>
      unfold primes
      simp
      norm_num
    case succ p =>
      linarith

lemma prime_pos {n p : Nat} (hp : p ∈ primes n) :
  0 < p := by
  have : 2 ≤ p := smallest_prime p hp
  linarith

lemma x_plus_one_le_exp_x (x : Real) :
  x + 1 ≤ Real.exp x := by
    exact add_one_le_exp x

lemma one_plus_x_le_exp_x (x : Real) :
  1 + x ≤ Real.exp x := by
    rw [add_comm]
    exact add_one_le_exp x

lemma prime_prod_le_exp_sum (n : Nat) :
  ∏ p ∈ primes n, (1 + r1 / p) ≤ rexp (∑ p ∈ primes n, r1 / p) := by
  unfold r1
  rw [exp_sum]
  have (x : Real) : 1 + 1 / x ≤ rexp (1 / x) := by
    rw [add_comm]
    apply add_one_le_exp
  calc
    ∏ p ∈ primes n, (1 + r1 / p) ≤ ∏ p ∈ primes n, rexp (1 / p) := by
      apply prod_le_prod
      case h0 =>
        intro p hp
        have : 0 < r1 / p := by
          apply one_div_pos.mpr
          exact_mod_cast prime_pos hp
        linarith
      case h1 =>
        intro p hp
        exact_mod_cast one_plus_x_le_exp_x (r1 / p)

lemma harmonic_upper (n : Nat) :
  ∑ i ∈ range n, (r1 / (i + 1)) ≤
    (∏ p ∈ primes n, (1 + r1 / p)) * ∑ i ∈ range n, (r1 / (i + 1) ^ 2) := by

  sorry

lemma harmonic_upper' (n : Nat) :
  ∑ i ∈ range n, r1 / (i + 1) ≤
    (∏ p ∈ primes n, (1 + r1 / p)) * 2 := by
  calc
    ∑ i ∈ range n, r1 / (i + 1) ≤
      (∏ p ∈ primes n, (1 + r1 / p)) * ∑ i ∈ range n, (r1 / (i + 1) ^ 2) := by
        apply harmonic_upper
    _ ≤ (∏ p ∈ primes n, (1 + r1 / p)) * 2 := by
      apply mul_le_mul_of_nonneg_left
      case h =>
        apply LT.lt.le
        exact sum_square_lt_two n
      case a0 =>
        apply prod_nonneg
        intro i hi
        apply prime_pos at hi
        unfold r1
        have : 0 < r1 / i := by
          apply one_div_pos.mpr
          exact_mod_cast hi
        apply LT.lt.le
        unfold r1 at this
        linarith


lemma lower_exp_prime_recip_sum (k : Nat) :
  (k + 1) / r2 ≤ rexp (∑ p ∈ primes (2 ^ k), r1 / p) * 2 := by
  let n := 2 ^ k
  calc
    (k + 1) / r2 ≤ ∑ i ∈ range n, r1 / (i + 1) := by
      apply half_log_le_sum
    _ ≤ (∏ p ∈ primes n, (1 + r1 / p)) * 2 := by
      apply harmonic_upper'
    _ ≤ rexp (∑ p ∈ primes n, r1 / p) * 2 := by
      apply mul_le_mul_of_nonneg_right
      swap
      norm_num
      exact prime_prod_le_exp_sum n

theorem log_log_le_prime_recip_sum (k : Nat) :
  log ((k + 1) / r4) ≤ ∑ p ∈ primes (2 ^ k), r1 / p := by
  apply exp_le_exp.mp
  calc
    rexp (log ((k + 1) / r4)) = (k + 1) / r4 := by
      apply exp_log
      unfold r4
      norm_num
      linarith
    _ ≤ rexp (∑ p ∈ primes (2 ^ k), r1 / p) := by
      calc
        (k + 1) / r4 = (k + 1) / 4 := by
          unfold r4
          rfl
        _ = (k + 1) / 2 / 2 := by
          field_simp
          norm_num
        _ ≤ (rexp (∑ p ∈ primes (2 ^ k), r1 / p) * 2) / 2 := by
          apply div_le_div₀
          all_goals norm_num
          swap
          apply lower_exp_prime_recip_sum
          apply LT.lt.le
          apply exp_pos
      simp

theorem exists_prime_larger_than (n : Nat) :
  ∃ p : Nat, n < p ∧ Nat.Prime p := by
  by_contra h
  have h' : ∀ m, n < m → ¬ Nat.Prime m := by
    intro m hm
    intro hpm
    apply h
    use m
  have few_primes (k : Nat) : primes k ⊆ Finset.range (n + 1) := by
    intro p hp
    unfold primes at hp
    apply Finset.mem_filter.mp at hp
    simp
    have : Nat.Prime p := hp.right
    by_contra hpn
    apply h' p
    swap
    exact this
    linarith
  have h_card (k : Nat): # (primes k) ≤ # (Finset.range (n + 1)) := by
    exact Finset.card_le_card (few_primes k)
  let M := ceil ( rexp (n + 1) * 4 )
  have small_recip_sum :
    ∑ p ∈ primes (2 ^ M), r1 / p ≤ n + 1 := by
    calc
      ∑ p ∈ primes (2 ^ M), r1 / p ≤ ∑ p ∈ primes (2 ^ M), 1 := by
        apply Finset.sum_le_sum
        intro p hp
        unfold r1
        apply smallest_prime at hp
        apply le_of_one_div_le_one_div
        norm_num
        field_simp
        linarith
      _ = # (primes (2 ^ M)) := by
        rw [Finset.sum_const]
        simp
      _ ≤ # (Finset.range (n + 1)) := by
        exact_mod_cast h_card (2 ^ M)
      _ = n + 1 := by
        rw [Finset.card_range]
        simp
  have large_recip_sum :
    log ((M + 1) / r4) ≤ ∑ p ∈ primes (2 ^ M), r1 / p := by
    apply log_log_le_prime_recip_sum
  have cmp : log ((M + 1) / r4) ≤ n + 1 := by
    calc
      log ((M + 1) / r4) ≤ ∑ p ∈ primes (2 ^ M), r1 / p := by
        exact large_recip_sum
      _ ≤ n + 1 := by
        exact small_recip_sum
  have hm : rexp (n + 1) * 4 ≤ M := by
    unfold M
    apply ceil_le.mp
    rfl
  have hm' : rexp (n + 1) * 4 < M + 1 := by
    calc
      rexp (n + 1) * 4 ≤ M := hm
      _ < M + 1 := by
        linarith
  have hm'' : rexp (n + 1) < (M + 1) / r4 := by
    unfold r4
    apply (lt_div_iff₀' (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hm''' : log (rexp (n + 1)) < log ((M + 1) / r4) := by
    apply Real.log_lt_log
    apply exp_pos
    exact hm''
  rw [Real.log_exp] at hm'''
  linarith
