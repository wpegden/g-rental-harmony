import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image

set_option linter.style.longLine false

open scoped BigOperators
open Finset

variable {n : ℕ} (hn : 0 < n)

lemma hall_condition_from_convex_hull
    (hn : 0 < n)
    (S : Finset (Fin n → ℝ))
    (P : Fin (n - 1) → (Fin n → ℝ) → Fin n)
    (h_conv : (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) ∈ convexHull ℝ (S.image (fun v => ∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ)) : Set (Fin n → ℝ))) :
    ∀ (K : Finset (Fin (n - 1))), K.Nonempty →
      (K.biUnion (fun j => S.image (fun v => P j v))).card ≥ K.card + 1 := by
  intro K hK_nonempty
  let R := K.biUnion (fun j => S.image (fun v => P j v))
  by_contra! h_contra
  have h_le_nat : R.card ≤ K.card := by
    change (K.biUnion (fun j => S.image (fun v => P j v))).card ≤ K.card
    omega
  have h_le : (R.card : ℝ) ≤ (K.card : ℝ) := Nat.cast_le.mpr h_le_nat
  rw [mem_convexHull'] at h_conv
  rcases h_conv with ⟨w, hw_pos, hw_sum, hw_eq⟩
  let y_v := fun v => ∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ)
  let ys := S.image y_v
  have h_LHS : ∑ i ∈ R, (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) i = R.card * ((n - 1 : ℝ) / (n : ℝ)) := by
    simp
  have h_RHS : ∑ i ∈ R, (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) i = ∑ i ∈ R, ∑ y ∈ ys, w y * y i := by
    apply sum_congr rfl
    intro i hi
    have h1 : ∑ y ∈ ys, w y • y = (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) := hw_eq
    have h2 : (∑ y ∈ ys, w y • y) i = (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) i := by rw [h1]
    rw [← h2, Finset.sum_apply]
    apply sum_congr rfl
    intro y hy
    rfl
  rw [h_LHS] at h_RHS
  have h_swap : ∑ i ∈ R, ∑ y ∈ ys, w y * y i = ∑ y ∈ ys, w y * (∑ i ∈ R, y i) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro y hy
    rw [mul_sum]
  rw [h_swap] at h_RHS
  have h_bound : ∀ y ∈ ys, (K.card : ℝ) ≤ ∑ i ∈ R, y i := by
    intro y hy
    simp only [ys, y_v, mem_image] at hy
    rcases hy with ⟨v, hv, rfl⟩
    have h_sum_eval : ∑ i ∈ R, (∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ)) i =
        ∑ j : Fin (n - 1), ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [Finset.sum_apply]
    rw [h_sum_eval]
    have h_inner : ∀ j ∈ K, ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i = 1 := by
      intro j hj
      have h_in_R : P j v ∈ R := by
        simp only [R, mem_biUnion, mem_image]
        use j, hj, v, hv
      rw [sum_eq_single (P j v)]
      · simp
      · intro i hi h_neq
        rw [Pi.single_apply]
        rw [if_neg h_neq]
      · intro h_not_in
        contradiction
    have h_ge : (K.card : ℝ) ≤ ∑ j ∈ K, ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i := by
      have h_eq_K : ∑ j ∈ K, ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i = ∑ j ∈ K, (1 : ℝ) := by
        apply sum_congr rfl
        exact h_inner
      rw [h_eq_K]
      simp
    have h_pos_all : ∀ j, 0 ≤ ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i := by
      intro j
      apply sum_nonneg
      intro i hi
      rw [Pi.single_apply]
      split_ifs
      · exact zero_le_one
      · rfl
    have h_super : ∑ j ∈ K, ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i ≤ ∑ j : Fin (n - 1), ∑ i ∈ R, (Pi.single (P j v) 1 : Fin n → ℝ) i := by
      apply sum_le_univ_sum_of_nonneg h_pos_all
    exact le_trans h_ge h_super
  have h_bound2 : (K.card : ℝ) ≤ ∑ y ∈ ys, w y * (∑ i ∈ R, y i) := by
    have h_le_sum : ∑ y ∈ ys, w y * (K.card : ℝ) ≤ ∑ y ∈ ys, w y * (∑ i ∈ R, y i) := by
      apply sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_left
      · exact h_bound y hy
      · exact hw_pos y hy
    have h_sum_w_K : ∑ y ∈ ys, w y * (K.card : ℝ) = (K.card : ℝ) := by
      rw [← sum_mul, hw_sum, one_mul]
    rwa [h_sum_w_K] at h_le_sum
  rw [← h_RHS] at h_bound2
  have h_bound3 : (K.card : ℝ) ≤ (K.card : ℝ) * ((n - 1 : ℝ) / (n : ℝ)) := by
    have h_n_pos : (0 : ℝ) ≤ ((n - 1 : ℝ) / (n : ℝ)) := by
      have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
        have h_ge_1 : 1 ≤ n := hn
        exact sub_nonneg.mpr (by exact_mod_cast h_ge_1)
      have h2 : (0 : ℝ) < n := by
        have h_pos : 0 < n := hn
        exact_mod_cast h_pos
      exact div_nonneg h1 (le_of_lt h2)
    calc
      (K.card : ℝ) ≤ (R.card : ℝ) * ((n - 1 : ℝ) / (n : ℝ)) := h_bound2
      _ ≤ (K.card : ℝ) * ((n - 1 : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_right h_le h_n_pos
  have hK_pos : (0 : ℝ) < K.card := by
    have h_card_pos : 0 < K.card := Finset.card_pos.mpr hK_nonempty
    exact_mod_cast h_card_pos
  have h_frac_ge_1 : 1 ≤ ((n - 1 : ℝ) / (n : ℝ)) := (le_mul_iff_one_le_right hK_pos).mp h_bound3
  have h_n_pos_strict : (0 : ℝ) < n := by exact_mod_cast hn
  have h_n_ge : (n : ℝ) ≤ (n : ℝ) - 1 := by
    have h_tmp := (le_div_iff₀ h_n_pos_strict).mp h_frac_ge_1
    rw [one_mul] at h_tmp
    exact h_tmp
  have h_contra_real : (n : ℝ) - 1 < (n : ℝ) := sub_one_lt (n : ℝ)
  exact (not_le.mpr h_contra_real) h_n_ge
