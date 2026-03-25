import PaperDefinitions
import Mathlib.Combinatorics.Hall.Basic

open scoped BigOperators
open Finset

variable {n : ℕ} (hn : 0 < n)

/-- Theorem 1 (Intermediate): Given n-1 valid preferences, there exists a maximal simplex
(n vertices) such that any k roommates collectively prefer at least k+1 distinct rooms
across its vertices. -/
theorem rental_harmony_hall (T : Triangulation n) (P : Fin (n - 1) → Preference n)
    (hP : ∀ j, ValidPreference T (P j)) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ (K : Finset (Fin (n - 1))),
        (K.biUnion (fun j => τ.image (fun v => P j v))).card ≥ K.card + 1 :=
  sorry

/-- Theorem 1 (Main): For an n-bedroom apartment it is sufficient to know the subjective preferences
of n-1 roommates to find an envy-free division of rent. This means there is a simplex τ representing
a rent division such that, no matter which room the secretive roommate chooses, there is a valid
assignment of the remaining rooms to the n-1 roommates where everyone gets a room they prefer at
one of the vertices of τ. -/
theorem rental_harmony_main (T : Triangulation n) (P : Fin (n - 1) → Preference n)
    (hP : ∀ j, ValidPreference T (P j)) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ (secret_room : Fin n),
        ∃ (assignment : Fin (n - 1) → Fin n),
          Function.Injective assignment ∧
          (∀ j, assignment j ≠ secret_room) ∧
          ∀ j, ∃ v ∈ τ, P j v = assignment j := by
  have h_hall := rental_harmony_hall T P hP
  rcases h_hall with ⟨τ, hτ_faces, hτ_card, h_hall_cond⟩
  refine ⟨τ, hτ_faces, hτ_card, fun secret_room => ?_⟩
  let t : Fin (n - 1) → Finset (Fin n) := fun j => (τ.image (fun v => P j v)) \ {secret_room}
  have h_hall' : ∀ (s : Finset (Fin (n - 1))), s.card ≤ (s.biUnion t).card := by
    intro s
    have h1 := h_hall_cond s
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
        Set (Fin (n + 1) → ℝ)) :=
  sorry

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
      ∀ j, (τ.image (fun v => L j v)).card ≥ k j :=
  sorry
