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
- [ ] Prove `rental_harmony_hall` (the Hall condition component)
- [ ] Prove `sperner_point_convex_hull`
- [ ] Prove `meunier_conjecture`

## Completed
- [x] Create `PaperDefinitions.lean` and `PaperTheorems.lean` following the combinatorial route at the repo root.
- [x] Move completed items here or check them off in place.
