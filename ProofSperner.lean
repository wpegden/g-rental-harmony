import PaperTheorems
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

open scoped BigOperators
open Finset

-- We need to prove `sperner_point_convex_hull`.
-- The algorithm in Section 5 defines a graph on the simplices.
-- Instead of doing the full geometric path following (which requires general position),
-- we can prove it using the purely combinatorial generalized Sperner's lemma (the vector labeling version).
-- Mathlib might not have this, so we will need to formalize a basic version of Scarf's algorithm,
-- or use a topological argument if we can find Brouwer.

-- Let's check if Mathlib has Brouwer Fixed Point Theorem.
-- `Mathlib.Topology.BrouwerFixedPoint` ?
