-- This module serves as the root of the `Four` library.
-- Import modules here that should be built as part of the library.

import Mathlib

open Nat Finset BigOperators Set

def r1 : Real := 1
def r2 : Real := 2

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

lemma sum_ge_half_log (k : Nat) : ∑ i ∈ range (2 ^ k), r1 / (i + 1) ≥ (k + 1) / r2 := by
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
  exact sum_ge_half_log k
  exact sum_le_log k

theorem sum_square_lt_two (k : Nat) :
  ∑ i ∈ range k, r1 / (i + 1) ^ 2 < r2 := by
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
