import PaperTheorems
import Mathlib.Analysis.Convex.Basic

open scoped BigOperators
open Finset

variable {n : ℕ} (hn : 0 < n)

-- Suppose we have a preference that is a Sperner labeling after a shift
def ShiftedSpernerPreference (T : Triangulation n) (P : Preference n) : Prop :=
  ∃ (f : Fin n → Fin n), Function.Bijective f ∧
    ∀ v ∈ T.complex.vertices, 0 < v (f (P v))

-- We can prove the Hall condition if the preferences are ShiftedSperner
lemma rental_harmony_hall_shifted (T : Triangulation n) (P : Fin (n - 1) → Preference n)
    (hP : ∀ j, ShiftedSpernerPreference T (P j)) :
    ∃ τ ∈ T.complex.faces, τ.card = n ∧
      ∀ (K : Finset (Fin (n - 1))),
        (K.biUnion (fun j => τ.image (fun v => P j v))).card ≥ K.card + 1 := by
  sorry
