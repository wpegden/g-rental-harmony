# Formalization Plan: Achieving Rental Harmony

## 1. Overview and Design Choices

The main mathematical result of the paper shows that given $n-1$ preferences on an $n$-bedroom apartment, one can find a fair rent division. The proof is based on a multi-labeling generalization of Sperner's lemma on triangulations of the standard simplex. The paper essentially proves the combinatorial result for any finite triangulation (since roommates do not care about 1-cent error margins).

**MAJOR DESIGN CHOICE (NEED_INPUT):**
How should we prove the Generalized Sperner's Lemma (the existence of a simplex mapping to the barycenter under a convex combination of PL maps)?
*   **Option A (Topological - Mathlib):** Construct the continuous Piecewise Linear (PL) map $\lambda: \Delta_n \to \Delta_n$ from the discrete labelings, and apply `Mathlib`'s topological tools (e.g., Brouwer Fixed Point Theorem) to deduce surjectivity. This requires defining the geometric realization and checking boundary conditions topologically.
*   **Option B (Combinatorial - Section 5):** Formalize the path-following "trap-door" algorithm presented in Section 5. This approach avoids continuous topology but requires formalizing general position/lexicographic perturbations to ensure graph vertex degrees are exactly 1 or 2.
*   **Option C (Axiomatize the core lemma):** If formalizing either approach from scratch is out of scope for this project, we could propose axiomatizing the vector-labeling generalization of Sperner's Lemma.

We will proceed by writing the definitions and theorem statements abstractly so that the final combinatorial theorems are independent of the proof method.

## 2. Definitions (`PaperDefinitions.lean`)

We will define the following core concepts using `Mathlib.Geometry.SimplicialComplex` and related affine geometry theories:

*   **`StandardSimplex n`**: The standard $(n-1)$-simplex in $\mathbb{R}^n$ (non-negative coordinates summing to 1).
*   **`Triangulation n`**: A geometric simplicial complex `T` covering `StandardSimplex n`.
*   **`SpernerLabeling T`**: A coloring $c: \text{vertices}(T) \to \{1, \dots, n\}$ such that for every vertex $v$, its color $c(v)$ corresponds to a non-zero coordinate of $v$ (i.e. $c(v) \in \text{carrier}(v)$).
*   **`Preference n`**: A function representing roommate preferences on the vertices of a triangulation, mapping to an available room.
*   **`BoundaryCondition`**: The condition that if free rooms exist (i.e., some coordinates of $v$ are 0), the preference must be one of the free rooms.

## 3. Main Theorems (`PaperTheorems.lean`)

**Theorem 1 (Combinatorial Rental Harmony):**
Given a triangulation $T$ of the $(n-1)$-simplex and $n-1$ preferences $P_1, \dots, P_{n-1}$ satisfying the free-room boundary condition, there exists a maximal simplex $\tau \in T$ such that across its $n$ vertices, any subset of $k$ roommates collectively prefers at least $k+1$ distinct rooms. (This guarantees a valid allocation by Hall's Marriage Theorem).

**Theorem 2 (Multi-labeling Sperner - Point convex hull):**
Given $m$ Sperner labelings $\lambda_1, \dots, \lambda_m$ on a triangulated $\Delta_n$, and a point $y \in m \cdot \Delta_n$ not in the convex hull of fewer than $n+1$ lattice points, there is a simplex $\tau \in T$ mapping to a set of $n+1$ lattice points whose convex hull contains $y$.

**Theorem 3 (Meunier Conjecture / Babson's Theorem):**
Given $m$ Sperner labelings of a triangulated $\Delta_n$ and integers $k_1, \dots, k_m \ge 1$ summing to $n+m$, there exists a simplex $\tau \in T$ on which each $\lambda_j$ exhibits at least $k_j$ distinct labels.

## 4. Proof Roadmap

1.  **Sperner Boundary Trick (Section 4):**
    *   Formalize the cyclic permutation trick. Let $F_v = \{i \mid v_i = 0\}$ be the set of free rooms. Show that we can always assign a free room $c \in F_v$ such that its cyclic predecessor $f^{-1}(c)$ has $v_{f^{-1}(c)} \neq 0$.
    *   This transforms the $n-1$ free-room preferences into $n-1$ valid `SpernerLabeling`s.
2.  **Combinatorics of the Barycenter:**
    *   Show that if a simplex $\tau$ has vertices whose average label vectors (under the $n-1$ labelings) convexly span the barycenter $\frac{1}{n} \mathbf{1}$, then the Hall Marriage condition holds: any $k$ roommates prefer at least $k+1$ rooms.
3.  **Generalized Sperner's Lemma (Pending Option A/B/C):**
    *   Prove (or assume, pending input) that for any convex combination of $m$ Sperner labelings, the image of some simplex $\tau$ under the PL extension contains the target point (barycenter).
4.  **Final Assembly:**
    *   Apply the Generalized Sperner's Lemma to the modified labelings from Step 1, concluding Step 2, and proving Theorem 1.
    *   Similarly apply the Lemma to prove Theorem 2 and 3.

## 5. Mathlib Dependencies

*   `Mathlib.Data.Fin.Basic`, `Mathlib.Data.Fintype.Basic`: For permutations, finite sets, and counting label occurrences.
*   `Mathlib.Geometry.SimplicialComplex.Basic`: For formalizing the triangulation of the simplex.
*   `Mathlib.Analysis.Convex.Basic`: For convex hulls and barycentric coordinates.
*   `Mathlib.Topology.BrouwerFixedPoint` (if pursuing Option A).
