import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

open scoped BigOperators

variable {n : ℕ}

/-- A triangulation of the standard simplex is a simplicial complex whose underlying space
is exactly the standard simplex. -/
structure Triangulation (n : ℕ) where
  complex : Geometry.SimplicialComplex ℝ (Fin n → ℝ)
  space_eq : complex.space = stdSimplex ℝ (Fin n)

/-- A preference assigns to each point a room (represented by a Fin n).
We define it globally for simplicity, but it only matters on the vertices. -/
def Preference (n : ℕ) :=
  (Fin n → ℝ) → Fin n

/-- The condition that if there are any free rooms (coordinates = 0),
the preferred room must be one of them. -/
def ValidPreference (T : Triangulation n) (P : Preference n) : Prop :=
  ∀ v ∈ T.complex.vertices, (∃ i, v i = 0) → v (P v) = 0

/-- A standard Sperner labeling requires that the label assigned to a vertex corresponds
to a strictly positive coordinate of that vertex. -/
def SpernerLabeling (T : Triangulation n) (L : (Fin n → ℝ) → Fin n) : Prop :=
  ∀ v ∈ T.complex.vertices, 0 < v (L v)
