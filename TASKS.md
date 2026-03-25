# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Prove the target statements presented in `PaperTheorems.lean`.
- [ ] Keep reusable proof infrastructure in separate support files when that yields a cleaner project structure.
- [ ] Maintain `TASKS.md` and `PLAN.md` as the proof frontier moves.
- [ ] Keep sorrys within the configured policy.
- [ ] Do not introduce unapproved axioms.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [x] Prove the Hall-condition-to-assignment step (`rental_harmony_main` from `rental_harmony_hall`)
- [x] Prove helper lemma about distinct preferred-room counts on a simplex from a convex combination (`hall_condition_from_convex_hull` in `HelperLemmas.lean`)
- [x] Prove `rental_harmony_hall` using `generalized_sperner_anti`
- [x] Formalize the combinatorial core of the trap-door algorithm (parity argument on abstract graph) in `TrapDoor.lean`
- [ ] Connect `TrapDoor.lean` to the geometric setting of triangulated simplices to prove `generalized_sperner_anti`
- [ ] Prove `sperner_point_convex_hull`
- [ ] Prove `meunier_conjecture`

## Completed
- [x] Create `PaperDefinitions.lean` and `PaperTheorems.lean` following the combinatorial route at the repo root.
- [x] Move completed items here or check them off in place.
