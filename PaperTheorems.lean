import PaperDefinitions
import ProofGeometry
import HelperLemmas
import Mathlib.Combinatorics.Hall.Basic

set_option linter.style.longLine false

open scoped BigOperators
open Finset

variable {n : ℕ} (hn : 0 < n)

/-- The core combinatorial statement of the Generalized Sperner's Lemma via vector labeling.
Given a triangulation and a vector assignment for each vertex that satisfies the
appropriate boundary condition (anti-Sperner), the target barycenter point is contained
in the convex hull of the assigned vectors of some top-dimensional simplex. -/
lemma generalized_sperner_anti
    (hn : 0 < n)
    (T : Triangulation n)
    (y : (Fin n → ℝ) → Fin n → ℝ)
    (hy_pos : ∀ v ∈ T.complex.vertices, ∀ i, 0 ≤ y v i)
    (hy_sum : ∀ v ∈ T.complex.vertices, ∑ i, y v i = n - 1)
    (hy_boundary : ∀ v ∈ T.complex.vertices, (∃ i : Fin n, v i = 0) → ∀ i : Fin n, v i > 0 → y v i = 0) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) ∈ convexHull ℝ (τ.image (fun v => y v)) := by
  -- We assume that the generic path-following bounds hold.
  -- In a full formalization of piecewise linear topology, these would be proven
  -- via lexicographic perturbation or generic intersection arguments.
  let b : ℕ → Fin n → ℝ := fun _ _ => ((n - 1 : ℝ) / (n : ℝ))
  have h_bounds : GeometricTrapDoorBounds T y b := sorry
  exact apply_geometric_trap_door T y b h_bounds

/-- Theorem 1 (Intermediate): Given n-1 valid preferences, there exists a maximal simplex
(n vertices) such that any k roommates collectively prefer at least k+1 distinct rooms
across its vertices. -/
theorem rental_harmony_hall (hn : 0 < n) (T : Triangulation n) (P : Fin (n - 1) → Preference n)
    (hP : ∀ j, ValidPreference T (P j)) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ (K : Finset (Fin (n - 1))), K.Nonempty →
        (K.biUnion (fun j => τ.image (fun v => P j v))).card ≥ K.card + 1 := by
  let y : (Fin n → ℝ) → Fin n → ℝ := fun v => ∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ)
  have hy_pos : ∀ v ∈ T.complex.vertices, ∀ i, 0 ≤ y v i := by
    intro v hv i
    simp only [y]
    rw [Finset.sum_apply]
    apply sum_nonneg
    intro j hj
    rw [Pi.single_apply]
    split_ifs
    · exact zero_le_one
    · rfl
  have hy_sum : ∀ v ∈ T.complex.vertices, ∑ i, y v i = n - 1 := by
    intro v hv
    simp only [y]
    have h_eval : ∑ i : Fin n, (∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ)) i = ∑ i : Fin n, ∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ) i := by
      apply sum_congr rfl
      intro i hi
      rw [Finset.sum_apply]
    rw [h_eval, sum_comm]
    have h1 : ∀ j, ∑ i : Fin n, (Pi.single (P j v) 1 : Fin n → ℝ) i = 1 := by
      intro j
      rw [sum_eq_single (P j v)]
      · rw [Pi.single_apply, if_pos rfl]
      · intro i hi hneq
        rw [Pi.single_apply, if_neg hneq]
      · intro hnot
        simp at hnot
    have h2 : ∑ j : Fin (n - 1), ∑ i : Fin n, (Pi.single (P j v) 1 : Fin n → ℝ) i = ∑ j : Fin (n - 1), (1 : ℝ) := by
      apply sum_congr rfl
      intro j hj
      exact h1 j
    rw [h2]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have h_ge : 0 < n := hn
    exact Nat.cast_pred h_ge
  have hy_boundary : ∀ v ∈ T.complex.vertices, (∃ i : Fin n, v i = 0) → ∀ i : Fin n, v i > 0 → y v i = 0 := by
    intro v hv h_free i h_pos
    simp only [y]
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro j hj
    have h_pref := hP j v hv h_free
    have h_neq : i ≠ P j v := by
      intro h_eq
      have h_eq_symm := h_eq.symm
      rw [h_eq_symm] at h_pref
      linarith
    rw [Pi.single_apply, if_neg h_neq]
  have h_sperner := generalized_sperner_anti hn T y hy_pos hy_sum hy_boundary
  rcases h_sperner with ⟨τ, hτ_faces, hτ_card, h_conv⟩
  refine ⟨τ, hτ_faces, hτ_card, ?_⟩
  -- We need to use `hall_condition_from_convex_hull`
  have h_conv' : (fun _ : Fin n => ((n - 1 : ℝ) / (n : ℝ))) ∈ convexHull ℝ (τ.image (fun v => ∑ j : Fin (n - 1), (Pi.single (P j v) 1 : Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact h_conv
  exact hall_condition_from_convex_hull hn τ P h_conv'

/-- Theorem 1 (Main): For an n-bedroom apartment it is sufficient to know the subjective preferences
of n-1 roommates to find an envy-free division of rent. This means there is a simplex τ representing
a rent division such that, no matter which room the secretive roommate chooses, there is a valid
assignment of the remaining rooms to the n-1 roommates where everyone gets a room they prefer at
one of the vertices of τ. -/
theorem rental_harmony_main (hn : 0 < n) (T : Triangulation n) (P : Fin (n - 1) → Preference n)
    (hP : ∀ j, ValidPreference T (P j)) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ (secret_room : Fin n),
        ∃ (assignment : Fin (n - 1) → Fin n),
          Function.Injective assignment ∧
          (∀ j, assignment j ≠ secret_room) ∧
          ∀ j, ∃ v ∈ τ, P j v = assignment j := by
  have h_hall := rental_harmony_hall hn T P hP
  rcases h_hall with ⟨τ, hτ_faces, hτ_card, h_hall_cond⟩
  refine ⟨τ, hτ_faces, hτ_card, fun secret_room => ?_⟩
  let t : Fin (n - 1) → Finset (Fin n) := fun j => (τ.image (fun v => P j v)) \ {secret_room}
  have h_hall' : ∀ (s : Finset (Fin (n - 1))), s.card ≤ (s.biUnion t).card := by
    intro s
    by_cases h_empty : s.Nonempty
    · have h1 := h_hall_cond s h_empty
      have h2 : s.biUnion t = (s.biUnion (fun j => τ.image (fun v => P j v))) \ {secret_room} := by
        ext x
        simp only [t, mem_biUnion, mem_sdiff, mem_singleton]
        tauto
      rw [h2]
      have h3 : ((s.biUnion (fun j => τ.image (fun v => P j v))) \ {secret_room}).card ≥
          (s.biUnion (fun j => τ.image (fun v => P j v))).card - 1 := by
        rw [sdiff_singleton_eq_erase]
        exact Finset.pred_card_le_card_erase
      omega
    · simp only [not_nonempty_iff_eq_empty] at h_empty
      rw [h_empty]
      simp only [card_empty, biUnion_empty, zero_le]
  have ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp h_hall'
  refine ⟨f, hf_inj, ?_, ?_⟩
  · intro j
    have : f j ∈ t j := hf_mem j
    simp only [t, mem_sdiff, mem_singleton] at this
    exact this.2
  · intro j
    have : f j ∈ t j := hf_mem j
    simp only [t, mem_sdiff, mem_singleton] at this
    have h_img := this.1
    simp only [mem_image] at h_img
    exact h_img

/-- Theorem 2: Given m Sperner labelings of a triangulation of Δ_n, and a point y in m * Δ_n
not in the convex hull of any n lattice points in m * Δ_n, there is a maximal simplex whose
corresponding lattice points contain y in their convex hull.
Note: Our `Triangulation (n+1)` corresponds to Δ_n, which has n+1 vertices. -/
theorem sperner_point_convex_hull {m : ℕ} (T : Triangulation (n + 1))
    (L : Fin m → (Fin (n + 1) → ℝ) → Fin (n + 1))
    (hL : ∀ j, SpernerLabeling T (L j))
    (y : Fin (n + 1) → ℝ)
    -- y is in m * Δ_n
    (hy_sum : ∑ i, y i = m) (hy_nonneg : ∀ i, 0 ≤ y i)
    -- y is not in the convex hull of any set of ≤ n lattice points (i.e. < n + 1)
    (h_generic : ∀ S : Finset (Fin (n + 1) → ℝ), S.card < n + 1 →
      (∀ x ∈ S, (∀ i, ∃ (k : ℕ), x i = (k : ℝ)) ∧ ∑ i, x i = m ∧ ∀ i, 0 ≤ x i) →
      y ∉ convexHull ℝ (S : Set (Fin (n + 1) → ℝ))) :
    ∃ τ ∈ T.complex.faces, τ.card = n + 1 ∧
      y ∈ convexHull ℝ (τ.image (fun v => ∑ j, (Pi.single (L j v) 1 : Fin (n + 1) → ℝ)) :
        Set (Fin (n + 1) → ℝ)) := by
  let y_vec : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun v => ∑ j, (Pi.single (L j v) 1 : Fin (n + 1) → ℝ)
  let b : ℕ → Fin (n + 1) → ℝ := fun k i => if k = n + 1 then y i else 0
  have h_bounds : GeometricTrapDoorBounds T y_vec b := sorry
  have hn_pos : 0 < n + 1 := Nat.succ_pos n
  have h_geom := apply_geometric_trap_door T y_vec b h_bounds
  rcases h_geom with ⟨τ, hτ_faces, hτ_card, h_conv⟩
  refine ⟨τ, hτ_faces, hτ_card, ?_⟩
  have h_eq : b (n + 1) = y := by
    ext i
    simp [b]
  rw [h_eq] at h_conv
  exact h_conv

/-- Theorem 3: Meunier Conjecture / Babson's Theorem
Given m Sperner labelings of a triangulation of Δ_n and positive integers k_j summing to n + m,
there exists a simplex τ where each labeling j exhibits at least k_j distinct labels. -/
theorem meunier_conjecture {m : ℕ} (T : Triangulation (n + 1))
    (L : Fin m → (Fin (n + 1) → ℝ) → Fin (n + 1))
    (hL : ∀ j, SpernerLabeling T (L j))
    (k : Fin m → ℕ)
    (hk_pos : ∀ j, 0 < k j)
    (hk_sum : ∑ j, k j = n + m) :
    ∃ τ ∈ T.complex.faces, τ.card = n + 1 ∧
      ∀ j, (τ.image (fun v => L j v)).card ≥ k j := by
  let α : Fin m → ℝ := fun j => (1 / ((n : ℝ) + 1)) * ((k j : ℝ) + 1 / (m : ℝ) - 1)
  let y_vec : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun v => ∑ j, α j • (Pi.single (L j v) 1 : Fin (n + 1) → ℝ)
  let b : ℕ → Fin (n + 1) → ℝ := fun k i => if k = n + 1 then 1 / ((n : ℝ) + 1) else 0
  have h_bounds : GeometricTrapDoorBounds T y_vec b := sorry
  have hn_pos : 0 < n + 1 := Nat.succ_pos n
  have h_geom := apply_geometric_trap_door T y_vec b h_bounds
  rcases h_geom with ⟨τ, hτ_faces, hτ_card, h_conv⟩
  refine ⟨τ, hτ_faces, hτ_card, ?_⟩
  -- The remainder is the algebraic/combinatorial deduction from h_conv
  sorry
