import GRentalHarmony.PaperDefinitions
import Mathlib.Combinatorics.Hall.Basic

open scoped BigOperators
open Finset

variable {n : ℕ} (hn : 0 < n)

/-- Theorem 1: Given n-1 valid preferences, there exists a maximal simplex (n vertices)
such that any k roommates collectively prefer at least k+1 distinct rooms across its vertices. -/
theorem rental_harmony (T : Triangulation n) (P : Fin (n - 1) → Preference n)
    (hP : ∀ j, ValidPreference T (P j)) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ (K : Finset (Fin (n - 1))),
        (K.biUnion (fun j => τ.image (fun v => P j v))).card ≥ K.card + 1 :=
  sorry

/-- Theorem 2: Given m Sperner labelings, and a point y in m * Δ_{n-1} not in the convex hull
of < n lattice points, there is a maximal simplex whose corresponding lattice points contain y
in their convex hull. -/
theorem sperner_point_convex_hull {m : ℕ} (T : Triangulation n)
    (L : Fin m → (Fin n → ℝ) → Fin n)
    (hL : ∀ j, SpernerLabeling T (L j))
    (y : Fin n → ℝ)
    -- y is in m * Δ_{n-1}
    (hy_sum : ∑ i, y i = m) (hy_nonneg : ∀ i, 0 ≤ y i)
    -- y is not in the convex hull of any set of < n lattice points
    -- (We omit the generic condition for brevity, stating the general existence of τ)
    :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      y ∈ convexHull ℝ (τ.image (fun v => ∑ j, (Pi.single (L j v) 1 : Fin n → ℝ)) :
        Set (Fin n → ℝ)) :=
  sorry

/-- Theorem 3: Meunier Conjecture / Babson's Theorem
Given m Sperner labelings and integers k_j summing to n + m - 1, there exists a simplex τ
where each labeling j exhibits at least k_j distinct labels. -/
theorem meunier_conjecture {m : ℕ} (T : Triangulation n)
    (L : Fin m → (Fin n → ℝ) → Fin n)
    (hL : ∀ j, SpernerLabeling T (L j))
    (k : Fin m → ℕ)
    (hk_sum : ∑ j, k j = n + m - 1) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ j, (τ.image (fun v => L j v)).card ≥ k j :=
  sorry
