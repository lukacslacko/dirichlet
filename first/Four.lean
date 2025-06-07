-- This module serves as the root of the `Four` library.
-- Import modules here that should be built as part of the library.

import Mathlib

open Nat Finset BigOperators Set

lemma sum_le_log (k : Nat) : ∑ i ∈ range (2 ^ k), (1 : Real) / (i + 1) ≤ (k + 1) := by
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
      ∑ x ∈ b \ a, (1 : Real) / (x + 1) = ∑ x ∈ c, (1 : Real) / (x + 1) := by rfl
      _ ≤ ∑ x ∈ c, 1 / (2 ^ k) := by
        apply Finset.sum_le_sum
        intro i hi
        apply le_of_one_div_le_one_div
        simp
        field_simp
        exact_mod_cast le_succ_of_le (h_lower i hi)
      _ = #c • (1 / (2 ^ k)) := by rw [Finset.sum_const]
      _ = 1 := by rw [h_card]; field_simp

lemma sum_ge_half_log (k : Nat) : ∑ i ∈ range (2 ^ k), (1 : Real) / (i + 1) ≥ (k + 1) / (2 : Real) := by
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

    have h_recip_lower: ∀ i ∈ c, (1 : Real) / (i + 1) ≥ (1 : Real) / (2 ^ (k + 1)) := by
      intro i hi
      apply le_of_one_div_le_one_div
      simp
      exact_mod_cast Nat.zero_lt_succ i
      field_simp
      have : i + 1 ≤ 2 ^ (k + 1) := by
        exact h_upper i hi
      exact_mod_cast this

    calc
      ∑ i ∈ c, (1 : Real) / (i + 1)
      ≥ ∑ i ∈ c, (1 : Real) / (2 ^ (k + 1)) := by
        apply Finset.sum_le_sum h_recip_lower
      _ = #c • ((1 : Real) / (2 ^ (k + 1))) := by
        rw [Finset.sum_const]
      _ = (2 ^ k) • ((1 : Real) / (2 ^ (k + 1))) := by
        rw [h_card]
      _ = (2 ^ k) * ((1 : Real) / (2 ^ (k + 1))) := by
        simp
      _ = (2 ^ k : Real) / (2 ^ (k + 1)) := by
        ring
      _ = (2 ^ k : Real) / (2 ^ k * 2) := by
        rw [pow_succ]
      _ = (1 : Real) / 2 := by
        field_simp

theorem sum_between_log (k : Nat) :
  (k + 1) / (2 : Real) ≤ ∑ i ∈ range (2 ^ k), (1 : Real) / (i + 1) ∧
  ∑ i ∈ range (2 ^ k), (1 : Real) / (i + 1) ≤ (k + 1) := by
  constructor
  exact sum_ge_half_log k
  exact sum_le_log k
