import Mathlib

open Finset Nat Set BigOperators

def DyadicSets : Nat → Finset Nat :=
  fun k => Finset.Ico (2 ^ k) (2 ^ (k + 1))

lemma dyadic_sum (k : Nat) (f: Nat → Nat) :
  ∑ i ∈ Finset.Ico 1 (2 ^ k), f i =
  ∑ i ∈ Finset.range k, ∑ j ∈ DyadicSets i, f j := by

  induction k

  case zero =>
    simp

  case succ k kh =>
    let first := Finset.Ico 1 (2 ^ k)
    let second := Finset.Ico (2 ^ k) (2 ^ (k + 1))
    let whole := Finset.Ico 1 (2 ^ (k + 1))
    have interval_halves_are_disjoint:
      Disjoint first second := by
      apply Finset.Ico_disjoint_Ico_consecutive
    have interval_halves_union:
      first ∪ second = whole := by
      apply Finset.Ico_union_Ico_eq_Ico
      case hbc =>
        apply Nat.pow_le_pow_right
        norm_num
        apply Nat.le_succ
      have : 1 = 2^0 := by norm_num
      rw [this]
      apply Nat.pow_le_pow_right
      norm_num
      apply Nat.zero_le
    have : ∑ i ∈ first ∪ second, f i =
      ∑ i ∈ first, f i + ∑ i ∈ second, f i := by
      apply Finset.sum_union interval_halves_are_disjoint
    rw [interval_halves_union] at this
    rw [this, kh]
    rw [Finset.sum_range_succ]
    simp
    unfold DyadicSets
    unfold second
    rfl
