import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.ZMod.Basic

set_option linter.style.longLine false

open scoped BigOperators
open Finset

variable {R D : Type} [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D]

/-- The core structure of a trap-door / path-following argument.
`R` is the set of "rooms" (e.g., simplices).
`D` is the set of "doors" (e.g., almost fully labeled facets).
`I` is the incidence relation (a door belongs to a room). -/
structure TrapDoorGraph (R D : Type) [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D] where
  I : R → D → Prop
  decI : DecidableRel I
  -- Each room has at most 2 doors
  room_doors_le_two : ∀ r : R, (univ.filter (fun d => I r d)).card ≤ 2
  -- Each door is shared by exactly 2 rooms, or exactly 1 room (boundary door)
  door_rooms_le_two : ∀ d : D, (univ.filter (fun r => I r d)).card ≤ 2
  door_rooms_pos : ∀ d : D, (univ.filter (fun r => I r d)).card > 0

namespace TrapDoorGraph

variable {R D : Type} [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D]
variable (G : TrapDoorGraph R D)

-- Let's make I decidable globally for convenience
attribute [local instance] TrapDoorGraph.decI

def room_degree (r : R) : ℕ := (univ.filter (fun d => G.I r d)).card
def door_degree (d : D) : ℕ := (univ.filter (fun r => G.I r d)).card

/-- The fundamental handshaking lemma for the trap door graph.
The sum of room degrees equals the sum of door degrees. -/
lemma sum_room_degree_eq_sum_door_degree :
    ∑ r : R, G.room_degree r = ∑ d : D, G.door_degree d := by
  have h1 : ∀ r : R, G.room_degree r = ∑ d : D, if G.I r d then 1 else 0 := by
    intro r
    exact (card_filter (fun d => G.I r d) univ)
  have h2 : ∀ d : D, G.door_degree d = ∑ r : R, if G.I r d then 1 else 0 := by
    intro d
    exact (card_filter (fun r => G.I r d) univ)
  simp only [h1, h2]
  exact sum_comm

lemma room_degree_parity :
    (univ.filter (fun r => G.room_degree r = 1)).card % 2 = (∑ r : R, G.room_degree r) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff' _ _ 2]
  push_cast
  have h_eq : ∀ r, (G.room_degree r : ZMod 2) = if G.room_degree r = 1 then (1 : ZMod 2) else 0 := by
    intro r
    have hr : G.room_degree r ≤ 2 := G.room_doors_le_two r
    split_ifs with h
    · rw [h]
      exact rfl
    · have h_zero_or_two : G.room_degree r = 0 ∨ G.room_degree r = 2 := by omega
      rcases h_zero_or_two with h0 | h2
      · rw [h0]
        exact rfl
      · rw [h2]
        exact rfl
  have h_sum_boole : ∑ r : R, (G.room_degree r : ZMod 2) = ∑ r : R, if G.room_degree r = 1 then (1 : ZMod 2) else 0 := by
    apply sum_congr rfl
    intro r _
    exact h_eq r
  rw [h_sum_boole]
  have h_filter : ∑ r : R, (if G.room_degree r = 1 then (1 : ZMod 2) else 0) = ((univ.filter (fun r => G.room_degree r = 1)).card : ZMod 2) := by
    have h_nat : (∑ r : R, if G.room_degree r = 1 then 1 else 0) = (univ.filter (fun r => G.room_degree r = 1)).card := by
      exact symm (card_filter (fun r => G.room_degree r = 1) univ)
    rw [← h_nat]
    push_cast
    rfl
  exact h_filter.symm

lemma door_degree_parity :
    (univ.filter (fun d => G.door_degree d = 1)).card % 2 = (∑ d : D, G.door_degree d) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff' _ _ 2]
  push_cast
  have h_eq : ∀ d, (G.door_degree d : ZMod 2) = if G.door_degree d = 1 then (1 : ZMod 2) else 0 := by
    intro d
    have hd : G.door_degree d ≤ 2 := G.door_rooms_le_two d
    split_ifs with h
    · rw [h]
      exact rfl
    · have h_zero_or_two : G.door_degree d = 0 ∨ G.door_degree d = 2 := by omega
      rcases h_zero_or_two with h0 | h2
      · rw [h0]
        exact rfl
      · rw [h2]
        exact rfl
  have h_sum_boole : ∑ d : D, (G.door_degree d : ZMod 2) = ∑ d : D, if G.door_degree d = 1 then (1 : ZMod 2) else 0 := by
    apply sum_congr rfl
    intro d _
    exact h_eq d
  rw [h_sum_boole]
  have h_filter : ∑ d : D, (if G.door_degree d = 1 then (1 : ZMod 2) else 0) = ((univ.filter (fun d => G.door_degree d = 1)).card : ZMod 2) := by
    have h_nat : (∑ d : D, if G.door_degree d = 1 then 1 else 0) = (univ.filter (fun d => G.door_degree d = 1)).card := by
      exact symm (card_filter (fun d => G.door_degree d = 1) univ)
    rw [← h_nat]
    push_cast
    rfl
  exact h_filter.symm

/-- If there is exactly one boundary door (degree 1), then there is at least one room of degree 1. -/
theorem trap_door_exists_room
    (h_one_door : (univ.filter (fun d => G.door_degree d = 1)).card = 1) :
    (univ.filter (fun r => G.room_degree r = 1)).card > 0 := by
  have hd : (univ.filter (fun d => G.door_degree d = 1)).card % 2 = 1 := by rw [h_one_door]
  have hr : (univ.filter (fun r => G.room_degree r = 1)).card % 2 = 1 := by
    calc
      (univ.filter (fun r => G.room_degree r = 1)).card % 2 = (∑ r : R, G.room_degree r) % 2 := room_degree_parity G
      _ = (∑ d : D, G.door_degree d) % 2 := by rw [sum_room_degree_eq_sum_door_degree]
      _ = (univ.filter (fun d => G.door_degree d = 1)).card % 2 := (door_degree_parity G).symm
      _ = 1 := hd
  omega

end TrapDoorGraph
