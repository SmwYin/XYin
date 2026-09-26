# Imaginary-axis and dimension-formula proof cleanup

## Scope and baseline

Worker-owned files `XYin/PhD/Modularforms/{ResToImagAxis,DimensionFormulas}.lean`,
compared with the supervisor snapshot `/tmp/xyin-proof-cleanup-before/XYin`.
Both complete files and all nontrivial proofs were inspected. All 69 public signatures
match the snapshot after whitespace normalization. No public mathematical definition
changed: the only definition-body edits are proof fields of `CuspForms_iso_Modforms`;
its forward map, inverse map, and all mathematical data remain unchanged.

| File | Before | After | Reduction | Original/final sorry declarations |
| --- | ---: | ---: | ---: | ---: |
| ResToImagAxis.lean | 480 | 403 | 77 | 0 / 0 |
| DimensionFormulas.lean | 509 | 200 | 309 | 10 / 1 |

## Source-backed mathematical changes

- The three private restriction homomorphism lemmas establish pointwise addition,
  multiplication, and real scalar multiplication once. Realness, positivity, and
  eventual positivity then use the ordinary real inequalities instead of repeatedly
  unfolding the dependent positive-half-line definition and complex coordinates.
- A private imaginary-axis convergence lemma uses
  `tendsto_comap_im_ofComplex` from
  `Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:78`.
  Both the big-O transfer and limit transfer now compose filters, instead of expanding
  epsilon/threshold definitions independently.
- `Mathlib/Analysis/Normed/Group/InfiniteSum.lean:140`, `tsum_of_norm_bounded`,
  bounds the Fourier expansion directly by the summable exponential majorant at
  height `c`. This replaces two separate auxiliary summability arguments and an
  unnecessary coarser exponential estimate. The mathematical comments identifying
  the real part of the exponent and the estimate for `y ≥ c` are retained next to
  the corresponding calculation; only obsolete summability-bridge comments were removed.
- `CuspForm.mulModularForm` directly supplies the cusp-form witness for multiplication
  by Delta. `IsCuspForm_weight_lt_eq_zero` now destructs the linear-map range membership
  and applies rank-zero vanishing, avoiding repeated coercion/projection identities.
- `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean` supplies
  `CuspForm.rank_eq_zero_of_weight_lt_twelve` (154),
  `ModularForm.rank_eq_one_add_rank_cuspForm` (170),
  `levelOne_weight_four_rank_one` (193), `levelOne_weight_six_rank_one` (198),
  and `ModularForm.dimension_level_one` (249). These replace the unfinished project
  proofs with direct specialization, keeping the exact existing statements.
- `Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean:59` supplies
  `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`. The local `Delta_E4_eqn` is now
  proved first from this pointwise identity, then supplies the scalar-existence and
  first-coefficient results. Moving the theorem earlier removes the old circular
  proof-sketch dependency without changing any declaration's signature.
- `Mathlib/Algebra/Order/Floor/Semifield.lean:47`, `Nat.floor_div_eq_div`,
  reconciles the rational-floor statement with mathlib's natural division formula.
  `Nat.floor_sub_one` and `Nat.add_sub_cancel'` replace the longer floor lemma proof.

The nine resolved original placeholders are `delta_eq_E4E6_const`,
`cuspform_weight_lt_12_zero`, `Delta_E4_E6_aux_q_one_term`, `Delta_E4_eqn`,
`weight_six_one_dimensional`, `weight_four_one_dimensional`,
`weight_eight_one_dimensional`, `dim_modforms_eq_one_add_dim_cuspforms`, and
`dim_modforms_lvl_one`. Their surrounding obsolete commented attempted proofs were
removed as explicitly requested by the supervisor/user. Mathematical module documentation,
public theorem explanations, and useful mathematical comments were preserved.
`dim_gen_cong_levels` remains the original unfinished finite-index subgroup result.

## Helper hygiene and alternatives assessed

- All four new `ResToImagAxis` helpers have multiple uses. The algebraic helpers only
  assume their operands; no unnecessary positivity premise is retained. The filter
  helper has no parameters. They stay private because they support this module's
  existing API rather than introducing a public interface merely to shorten proofs.
- The two private rank-transport helpers are separately reused by modular-form and
  cusp-form results. They take only the weight. A naive `rw [Gamma_one_coe_eq_SL]`
  directly on `Module.rank` failed because the motive contains the determinant-one
  instance used to construct its module structure. Binding `[G.HasDetOne]` while
  transporting the subgroup keeps the dependent instance valid; rewriting the
  concrete subgroup/range directly did not solve this issue.
- Global simp unfolds the dot-notation alias before the algebraic restriction helpers
  can match. The final closure proofs use `simp only` with precisely those helpers.
  No global simp attributes, priorities, or instances were changed.
- A rational numeral did not match `Nat.floor_div_eq_div` in an untyped simp list.
  A typed one-line `hfloor` supplies the intended coercions without new public helpers.
- `dim_modforms_lvl_one` retains its original named hypothesis `hk : 3 ≤ (k : ℤ)`
  even though the stronger mathlib formula does not require it. Its unused-variable
  warning is reported, rather than renaming/deleting a public named argument or
  inventing an artificial proof dependency. No linter was disabled.
- `rfl`, `exact`/`simpa`, filter composition, `omega`, `ring`, `norm_num`, and a
  single final `nlinarith` after the explicit exponential estimate were sufficient.
  No broad tactic search or manual analytic re-proofs were needed.

## Declaration-by-declaration proof audit

Line counts below omit blanks/comments, include the `by` line, and count all fields
for the one linear-equivalence declaration. Old two-line `by sorry` bodies are marked
by the resolved-placeholder list above; their short old size is not a completed proof.
Unchanged short wrappers, definitions, and induction proofs were reviewed and retained.

| Declaration | Before proof lines | After proof lines |
| --- | ---: | ---: |
| `ResToImagAxis` | 1 | 1 |
| `resToImagAxis` | 1 | 1 |
| `resToImagAxis_eq_resToImagAxis` | 1 | 1 |
| `resToImagAxis_apply` | 1 | 1 |
| `ResToImagAxis.Real` | 1 | 1 |
| `ResToImagAxis.Pos` | 1 | 1 |
| `ResToImagAxis.EventuallyPos` | 1 | 1 |
| `ResToImagAxis.Differentiable` | 13 | 13 |
| `ResToImagAxis.SlashActionS` | 8 | 8 |
| `ResToImagAxis.Real.const` | 3 | 3 |
| `ResToImagAxis.Real.zero` | 1 | 1 |
| `ResToImagAxis.Real.one` | 1 | 1 |
| `ResToImagAxis.Real.neg` | 5 | 3 |
| `ResToImagAxis.Real.add` | 6 | 3 |
| `ResToImagAxis.Real.sub` | 2 | 2 |
| `ResToImagAxis.Real.mul` | 6 | 4 |
| `ResToImagAxis.Real.smul` | 5 | 3 |
| `ResToImagAxis.Real.pow` | 4 | 4 |
| `ResToImagAxis.Pos.const` | 1 | 1 |
| `ResToImagAxis.Pos.one` | 1 | 1 |
| `ResToImagAxis.Pos.add` | 7 | 3 |
| `ResToImagAxis.Pos.mul` | 10 | 4 |
| `ResToImagAxis.Pos.smul` | 8 | 3 |
| `ResToImagAxis.Pos.pow` | 4 | 4 |
| `ResToImagAxis.EventuallyPos.from_pos` | 4 | 2 |
| `ResToImagAxis.EventuallyPos.one` | 1 | 1 |
| `ResToImagAxis.EventuallyPos.const` | 1 | 1 |
| `ResToImagAxis.EventuallyPos.add` | 18 | 6 |
| `ResToImagAxis.EventuallyPos.mul` | 22 | 10 |
| `ResToImagAxis.EventuallyPos.pow` | 4 | 4 |
| `ResToImagAxis.EventuallyPos.smul` | 12 | 4 |
| `ResToImagAxis.Real.eq_real_part` | 5 | 5 |
| `isBigO_resToImagAxis_of_isBigO_atImInfty` | 10 | 7 |
| `tendsto_rpow_mul_of_isBigO_exp` | 5 | 5 |
| `tendsto_rpow_mul_resToImagAxis_of_isBigO_exp` | 1 | 1 |
| `cuspForm_rpow_mul_resToImagAxis_tendsto_zero` | 8 | 8 |
| `isBigO_atImInfty_of_fourier_shift` | 50 | 15 |
| `tendsto_rpow_mul_resToImagAxis_of_fourier_shift` | 2 | 2 |
| `ResToImagAxis.Real.im_eq_zero_at` | 2 | 2 |
| `ResToImagAxis.Pos.re_pos_at` | 2 | 2 |
| `tendsto_resToImagAxis_of_tendsto_atImInfty` | 12 | 5 |
| `mul_Delta_map` | 4 | 4 |
| `mcast_apply` | 2 | 2 |
| `mul_Delta_map_eq` | 3 | 2 |
| `mul_Delta_map_eq_mul` | 3 | 2 |
| `qExpansion_coe_smul` | 1 | 1 |
| `qExpansion_coe_smul_cusp` | 1 | 1 |
| `qExpansion_coe_sub` | 1 | 1 |
| `mul_Delta_IsCuspForm` | 11 | 5 |
| `Modform_mul_Delta'` | 1 | 1 |
| `SlashInvariantForm.mul_apply` | 1 | 1 |
| `Modform_mul_Delta_apply` | 7 | 4 |
| `CuspForms_iso_Modforms` | 23 | 19 |
| `delta_eq_E4E6_const` | 2 | 2 |
| `cuspform_weight_lt_12_zero` | 2 | 2 |
| `IsCuspForm_weight_lt_eq_zero` | 13 | 4 |
| `Delta_E4_E6_eq` | 3 | 3 |
| `Delta_E4_E6_aux_q_one_term` | 2 | 3 |
| `Delta_E4_eqn` | 2 | 10 |
| `weight_six_one_dimensional` | 2 | 2 |
| `weight_four_one_dimensional` | 2 | 2 |
| `weight_eight_one_dimensional` | 2 | 4 |
| `weight_two_zero` | 4 | 4 |
| `dim_modforms_eq_one_add_dim_cuspforms` | 2 | 3 |
| `dim_weight_two` | 4 | 2 |
| `floor_lem1` | 9 | 3 |
| `dim_modforms_lvl_one` | 2 | 7 |
| `ModularForm.dimension_level_one_XYin` | 2 | 2 |
| `dim_gen_cong_levels` | 1 | 1 |

## Verification and remaining gates

- Actual `lake env lean XYin/PhD/Modularforms/ResToImagAxis.lean`: exit 0,
  no diagnostics (`/tmp/xyin-cleanup-res.log`). Subsequent changes only restored
  mathematical comments and normalized line wrapping/EOF. The final source copy
  also compiled in the profiler/axiom run below.
- Actual `lake env lean XYin/PhD/Modularforms/DimensionFormulas.lean`: exit 0
  (`/tmp/xyin-cleanup-dimension.log`), with the documented retained named-hypothesis
  warning and the original final `sorry` warning.
- Source-based signature audit: `/tmp/xyin-imag-dimension-audit.py` and its JSON
  output verify all 41 + 28 public signatures; no declarations removed.
- Final source copies with appended `#print axioms` were compiled using
  `lake env lean -Dprofiler=true -Dprofiler.threshold=100`:
  `/tmp/xyin-ResToImagAxis-profile-axioms.log` and
  `/tmp/xyin-DimensionFormulas-profile-axioms.log`.
  Both exited 0. The profiler reported no individual non-import operation at the
  100 ms threshold. Imports took 2.84 s and 3.47 s respectively; these are excluded
  from proof elaboration costs. No slow-proof queue or resource-limit workaround arose.
- Axioms: every one of the 41 Res declarations uses only a subset of `propext`,
  `Classical.choice`, `Quot.sound`. Of Dimension's 28 declarations, 23 use only that
  set. Four Delta/Eisenstein-identity declarations (`delta_eq_E4E6_const`,
  `Delta_E4_E6_eq`, `Delta_E4_E6_aux_q_one_term`, `Delta_E4_eqn`) still inherit
  `sorryAx` through the imported `Delta_E4_E6_aux` definition. The fifth is the
  retained `dim_gen_cong_levels` placeholder. These are not claimed axiom-clean.
- No new `sorry`, `axiom`, `admit`, `native_decide`, resource-limit raise, or profiling
  scaffolding was added to project source. `git diff --check` passes.

The supervisor owns independent simplify review and cumulative `lake build`; those
integration gates are not claimed as worker-run. Both source files are frozen.

## Deterministic performance cross-check

Temporary copies counted heartbeats with `#count_heartbeats in` and
`lake env lean -DElab.async=false`; no wrappers or options were added to project files.
Disabling asynchronous elaboration in these measurement copies is necessary to count
the proof task rather than only its scheduling. Before/after copies used the same
current imports and kept their respective original/final proof bodies.

| Declaration | Before heartbeats | After heartbeats | Reduction |
| --- | ---: | ---: | ---: |
| `isBigO_atImInfty_of_fourier_shift` | 11707 | 3299 | 71.8% |
| `tendsto_resToImagAxis_of_tendsto_atImInfty` | 483 | 274 | 43.3% |
| `mul_Delta_IsCuspForm` | 1180 | 985 | 16.5% |
| `floor_lem1` | 1082 | 777 | 28.2% |

All four measurement commands exited 0. Logs are
`/tmp/xyin-ResToImagAxis-{before,after}-heartbeat.log` and
`/tmp/xyin-DimensionFormulas-{before,after}-heartbeat.log`.
The Res baseline also confirms the removed unreachable `assumption` warning.
An initial measurement put command wrappers after docstrings, which produced parse
errors; those results were discarded, then the temporary copies were regenerated
without comments and rerun successfully.

## Final integration update

The coordinator subsequently proved `E4E6_coeff_zero_eq_zero` in `Eisenstein.lean`,
removing the upstream admission inherited by the four Delta results noted in the worker-time
axiom audit. The final compiled audit is recorded in `verification.md` and `axiom-audit.txt`;
only `dim_gen_cong_levels` remains admitted. The earlier audit above is historical evidence,
not the final dependency state.
