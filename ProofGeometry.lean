import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import PaperDefinitions
import TrapDoor

set_option linter.style.longLine false

open scoped BigOperators
open Finset

open Classical
noncomputable section

variable {n : ℕ} (hn : 0 < n)
variable (T : Triangulation n)
variable (y : (Fin n → ℝ) → Fin n → ℝ)
variable (b : ℕ → Fin n → ℝ)

-- A segment between two points
def Segment (p q : Fin n → ℝ) : Set (Fin n → ℝ) :=
  { x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (fun i => (1 - t) * p i + t * q i) }

def is_room (sigma : Finset (Fin n → ℝ)) : Prop :=
  sigma ∈ T.complex.faces ∧ sigma.card = n ∧
  ∃ pt ∈ convexHull ℝ (sigma.image y : Set (Fin n → ℝ)), pt ∈ Segment (b (n-1)) (b n)

def is_door (tau : Finset (Fin n → ℝ)) : Prop :=
  tau ∈ T.complex.faces ∧ tau.card = n - 1 ∧
  ∃ pt ∈ convexHull ℝ (tau.image y : Set (Fin n → ℝ)), pt ∈ Segment (b (n-1)) (b n)

def GeomRoom := { sigma : Finset (Fin n → ℝ) // is_room T y b sigma }
def GeomDoor := { tau : Finset (Fin n → ℝ) // is_door T y b tau }

def geom_incidence (r : GeomRoom T y b) (d : GeomDoor T y b) : Prop :=
  d.val ⊆ r.val

section TrapDoorGraphConstruction
variable [Fintype (GeomRoom T y b)] [Fintype (GeomDoor T y b)]
variable [DecidableRel (geom_incidence T y b)]

def build_trap_door_graph
    (h_room_le_two : ∀ r : GeomRoom T y b, (univ.filter (fun d => geom_incidence T y b r d)).card ≤ 2)
    (h_door_le_two : ∀ d : GeomDoor T y b, (univ.filter (fun r => geom_incidence T y b r d)).card ≤ 2)
    (h_door_pos : ∀ d : GeomDoor T y b, (univ.filter (fun r => geom_incidence T y b r d)).card > 0) :
    TrapDoorGraph (GeomRoom T y b) (GeomDoor T y b) where
  I := geom_incidence T y b
  decI := inferInstance
  room_doors_le_two := h_room_le_two
  door_rooms_le_two := h_door_le_two
  door_rooms_pos := h_door_pos

lemma exists_fully_labeled_simplex_from_geom
    (h_room_le_two : ∀ r : GeomRoom T y b, (univ.filter (fun d => geom_incidence T y b r d)).card ≤ 2)
    (h_door_le_two : ∀ d : GeomDoor T y b, (univ.filter (fun r => geom_incidence T y b r d)).card ≤ 2)
    (h_door_pos : ∀ d : GeomDoor T y b, (univ.filter (fun r => geom_incidence T y b r d)).card > 0)
    (h_one_door : (univ.filter (fun d : GeomDoor T y b => (univ.filter (fun r => geom_incidence T y b r d)).card = 1)).card = 1)
    (h_target : ∀ r : GeomRoom T y b, (univ.filter (fun d => geom_incidence T y b r d)).card = 1 →
      b n ∈ convexHull ℝ (r.val.image y : Set (Fin n → ℝ))) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      b n ∈ convexHull ℝ (τ.image y : Set (Fin n → ℝ)) := by
  let G := build_trap_door_graph T y b h_room_le_two h_door_le_two h_door_pos
  have h_room_pos_deg := TrapDoorGraph.trap_door_exists_room G h_one_door
  have h_exists_room : ∃ r ∈ univ, G.room_degree r = 1 := by
    have h_nonempty := card_pos.mp h_room_pos_deg
    rcases h_nonempty with ⟨r, hr⟩
    simp only [mem_filter, mem_univ, true_and] at hr
    exact ⟨r, mem_univ r, hr⟩
  rcases h_exists_room with ⟨r, _, hr⟩
  have h_spans := h_target r hr
  use r.val
  exact ⟨r.property.1, r.property.2.1, h_spans⟩

end TrapDoorGraphConstruction

structure GeometricTrapDoorBounds : Prop where
  fintype_room : Nonempty (Fintype (GeomRoom T y b))
  fintype_door : Nonempty (Fintype (GeomDoor T y b))
  dec_inc : Nonempty (DecidableRel (geom_incidence T y b))
  room_le_two : ∀ [Fintype (GeomDoor T y b)] [DecidableRel (geom_incidence T y b)], ∀ r : GeomRoom T y b, ((@univ (GeomDoor T y b) _).filter (fun d => geom_incidence T y b r d)).card ≤ 2
  door_le_two : ∀ [Fintype (GeomRoom T y b)] [DecidableRel (geom_incidence T y b)], ∀ d : GeomDoor T y b, ((@univ (GeomRoom T y b) _).filter (fun r => geom_incidence T y b r d)).card ≤ 2
  door_pos : ∀ [Fintype (GeomRoom T y b)] [DecidableRel (geom_incidence T y b)], ∀ d : GeomDoor T y b, ((@univ (GeomRoom T y b) _).filter (fun r => geom_incidence T y b r d)).card > 0
  one_door : ∀ [Fintype (GeomRoom T y b)] [Fintype (GeomDoor T y b)] [DecidableRel (geom_incidence T y b)], ((@univ (GeomDoor T y b) _).filter (fun d => ((@univ (GeomRoom T y b) _).filter (fun r => geom_incidence T y b r d)).card = 1)).card = 1
  target : ∀ [Fintype (GeomDoor T y b)] [DecidableRel (geom_incidence T y b)], ∀ r : GeomRoom T y b, ((@univ (GeomDoor T y b) _).filter (fun d => geom_incidence T y b r d)).card = 1 → b n ∈ convexHull ℝ (r.val.image y : Set (Fin n → ℝ))

lemma apply_geometric_trap_door
    (h_bounds : GeometricTrapDoorBounds T y b) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      b n ∈ convexHull ℝ (τ.image y : Set (Fin n → ℝ)) := by
  have inst1 : Fintype (GeomRoom T y b) := h_bounds.fintype_room.some
  have inst2 : Fintype (GeomDoor T y b) := h_bounds.fintype_door.some
  have inst3 : DecidableRel (geom_incidence T y b) := h_bounds.dec_inc.some
  exact exists_fully_labeled_simplex_from_geom T y b h_bounds.room_le_two h_bounds.door_le_two h_bounds.door_pos h_bounds.one_door h_bounds.target

-- PERTURBATION STRATEGY
-- We define a property indicating that the target point is generic with respect to
-- the faces of dimension < n-1.
def GenericTarget : Prop :=
  ∀ F ∈ T.complex.faces, F.card < n - 1 → b n ∉ convexHull ℝ (F.image y : Set (Fin n → ℝ))

lemma generic_implies_bounds (h_gen : GenericTarget T y b) : GeometricTrapDoorBounds T y b := by
  sorry

-- Because there are finitely many faces, we can avoid the bad affine spans.
-- If we perturb along a generic line u, b_t = b + t * u will be generic for almost all small t.
lemma exists_generic_perturbation :
    ∃ u : Fin n → ℝ, ∀ ε > 0, ∃ t ∈ Set.Ioo 0 ε, GenericTarget T y (fun k => if k = n then (fun i => b n i + t * u i) else b k) := by
  sorry

-- The limit argument: since T is finite, there exists one face τ that works for infinitely many t -> 0.
-- Since the convex hull is compact (closed), b n must be in the hull of τ for t=0.
lemma generic_limit_exists_simplex
    (h_perturbed : ∀ u : Fin n → ℝ, ∀ t > 0, ∃ τ ∈ T.complex.faces, τ.card = n ∧
      (fun i => b n i + t * u i) ∈ convexHull ℝ (τ.image y : Set (Fin n → ℝ))) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      b n ∈ convexHull ℝ (τ.image y : Set (Fin n → ℝ)) := by
  sorry

-- Combined Perturbation-Limit theorem
-- If we can prove bounds for any GenericTarget, we can prove the existence for any target b.
lemma exists_fully_labeled_simplex_via_perturbation :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      b n ∈ convexHull ℝ (τ.image y : Set (Fin n → ℝ)) := by
  sorry

