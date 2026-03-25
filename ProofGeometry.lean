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

-- To form a TrapDoorGraph, we need Fintypes.
-- We can just define R and D as the subtypes.
def GeomRoom := { sigma : Finset (Fin n → ℝ) // is_room T y b sigma }
def GeomDoor := { tau : Finset (Fin n → ℝ) // is_door T y b tau }

-- Incidence is just subset
def geom_incidence (r : GeomRoom T y b) (d : GeomDoor T y b) : Prop :=
  d.val ⊆ r.val

variable [Fintype (GeomRoom T y b)] [Fintype (GeomDoor T y b)]
variable [DecidableRel (geom_incidence T y b)]

/-- We construct the TrapDoorGraph assuming the geometric degree bounds hold. -/
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

/-- If the geometric graph satisfies the bounds and has exactly one boundary door,
    then there is a fully labeled simplex. -/
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
