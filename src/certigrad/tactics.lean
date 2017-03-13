/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous tactics.
-/
import .tfacts

namespace tactic

meta def simp_lemmas.append_simp : simp_lemmas → list name → tactic simp_lemmas
| sls []      := return sls
| sls (l::ls) := do
  new_sls ← simp_lemmas.add_simp sls l,
  simp_lemmas.append_simp new_sls ls

meta def simp_lemmas.from_names (names : list name) : tactic simp_lemmas :=
  simp_lemmas.append_simp simp_lemmas.mk names

meta definition dec_triv : tactic unit :=
do { tgt  ← target,
     inst ← to_expr ``(decidable %%tgt) >>= mk_instance,
     to_expr ``(@of_as_true %%tgt %%inst trivial) >>= exact }
<|>
do { fail "dec_triv failed" }

meta def at_target (tac : expr → tactic (expr × expr)) : tactic unit :=
  do tgt ← target,
     (new_tgt, pf) ← tac tgt,
     n ← mk_fresh_name,
     assert n new_tgt, swap,
     ht ← get_local n,
     mk_app `eq.mpr [pf, ht] >>= exact

meta def fsimpt (ns : list name) (tac : tactic unit) : tactic unit := do
  s ← list.mfoldl (λ slss n, simp_lemmas.add_simp slss n) simp_lemmas.mk ns,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s tac r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def at_hyp (n : name) (tac : expr → tactic (expr × expr)) : tactic unit :=
do h ← get_local n,
   h_type ← infer_type h,
   (new_h_type, pf) ← tac h_type,
   assert (expr.local_pp_name h) new_h_type,
   mk_eq_mp pf h >>= exact,
   try $ clear h

meta def norm_all_nums : tactic unit :=
  let norm_conv : conv unit := (λ (n : name) (e : expr),
                                  do guard (n = `eq),
                                     trace "\nabout to norm num: ", trace e,
                                     (new_val, pf) ← norm_num e,
                                     trace "\nsuccess: ", trace new_val,
                                     return ⟨(), new_val, some pf⟩) in
  at_target (conv.to_tactic (conv.bottom_up norm_conv) `eq)


meta def refs_neq : tactic unit :=
  assumption <|> (mk_const `pair_neq_of_neq₁ >>= apply >> assumption) <|> dec_triv

meta def dget_dinsert : tactic unit := do
  s ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.env.get_insert_same >>= flip simp_lemmas.add_simp `certigrad.env.get_insert_diff,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s refs_neq r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def cheat_refs_neq : tactic unit :=
do (lhs, rhs) ← target >>= match_ne,
   if lhs = rhs then failed else mk_sorry >>= exact

meta def dget_dinsert_cheat : tactic unit := do
  s ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.env.get_insert_same >>= flip simp_lemmas.add_simp `certigrad.env.get_insert_diff,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s cheat_refs_neq r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def dget_dinsert_at (n : name) : tactic unit := do
  s ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.env.get_insert_same >>= flip simp_lemmas.add_simp `certigrad.env.get_insert_diff,
  at_hyp n (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s refs_neq r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def refs_neq_concrete : tactic unit := /- applyc `pair_neq_of_neq₁ >> -/ dec_triv

meta def dget_dinsert_concrete : tactic unit := do
  s ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.env.get_insert_same >>= flip simp_lemmas.add_simp `certigrad.env.get_insert_diff,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s refs_neq_concrete r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def simp_dec_triv : tactic unit := do
  s ← simp_lemmas.mk_default,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s dec_triv r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

--meta def sdunfold : list name → tactic unit :=
--λ cs, target >>= dunfold_core semireducible default_max_steps cs >>= change

meta def gemm_get_col_range : tactic unit := do
  s ← simp_lemmas.from_names [`T.get_col_range_append_col],

  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s assumption r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))


meta def whnf_args : tactic unit := do
  tgt ← target,
  fn ← return (expr.get_app_fn tgt),
  args ← return (expr.get_app_args tgt),
  args' ← monad.mapm (λ arg, whnf arg semireducible) args,
  change (expr.mk_app fn args')

meta def simplify_dec_triv : tactic unit := do
  s ← simp_lemmas.mk_default,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s dec_triv r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def forall_mem_core (tac : tactic unit) : expr → tactic unit
| `(list.mem %%x₀ list.nil) := exfalso >> get_local `_H_mem >>= λ H_mem, to_expr ``(list.not_mem_nil %%x₀ %%H_mem) >>= exact
| `(list.mem %%x₀ (list.cons %%x %%xs)) :=
do H_mem ← get_local `_H_mem,
   to_expr ``(list.eq_or_mem_of_mem_cons %%H_mem) >>= λ e, cases e [`_H_eq, `_H_mem],
   clear H_mem,
   get_local `_H_eq >>= subst,
   solve1 tac,
   get_local `_H_mem >>= infer_type >>= forall_mem_core
| _ := fail "forall_mem_core: unexpected branch"

meta def forall_mem (tac : tactic unit) : tactic unit :=
do x ← intro1,
   H_mem ← intro `_H_mem,
   infer_type H_mem >>= forall_mem_core tac

meta def prove_mem : tactic unit :=
applyc `list.mem_cons_self <|> (applyc `list.mem_cons_of_mem >> prove_mem)

meta def prove_sublist : tactic unit :=
forall_mem prove_mem

meta def prove_contains : tactic unit :=
  triv
  <|>
  solve1 (applyc `certigrad.env.has_key_insert_same)
  <|>
  (applyc `certigrad.env.has_key_insert >> prove_contains)

meta def prove_all_ps_in_env : tactic unit :=
do whnf_target,
   triv <|> (applyc `and.intro >> solve1 (forall_mem prove_contains) >> solve1 (intro1 >> prove_all_ps_in_env))

meta def prove_fresh_core : expr → tactic unit
| `(list.mem %%x₀ list.nil) := exfalso >> get_local `_H_mem >>= λ H_mem, to_expr ``(list.not_mem_nil %%x₀ %%H_mem) >>= exact
| `(list.mem %%x₀ (list.cons %%x %%xs)) :=
do H_mem ← get_local `_H_mem,
   to_expr ``(list.eq_or_mem_of_mem_cons %%H_mem) >>= λ e, cases e [`_H_eq, `_H_mem],
   H_eq ← get_local `_H_eq,
   (lhs, rhs) ← infer_type H_eq >>= match_eq,
   mk_app `ne [lhs, rhs] >>= assert `H_neq,
   dec_triv,
   get_local `H_neq >>= λ H_neq, exact (expr.app H_neq H_eq),
   get_local `_H_mem >>= prove_fresh_core
| _ := fail "prove_fresh_core: unexpected branch"

meta def prove_fresh : tactic unit :=
do H_mem ← intro `_H_mem,
   infer_type H_mem >>= prove_fresh_core

meta def is_mem : expr → option (expr × expr)
| `(list.mem %%x %%xs) := some (x, xs)
| _                 := none

meta def match_mem (e : expr) : tactic (expr × expr) :=
match (is_mem e) with
| (some (x, xs)) := return (x, xs)
| none           := fail "expression is not of the form x ∈ xs"
end

meta def prove_grads_exist_at : tactic unit :=
do triv
   <|>
   solve1 (do { H_in_parents ← intro1,
                H_in_parents_type ← infer_type H_in_parents,
                (lhs, rhs) ← match_mem H_in_parents_type,
                assert `H_notin_parents (expr.app (expr.const `not []) H_in_parents_type),
                dec_triv,
                H_notin_parents ← get_local `H_notin_parents,
                tgt ← target,
                pr ← mk_app `false.rec [tgt, expr.app H_notin_parents H_in_parents],
                exact pr })
   <|>
   do { intro1, solve1 prove_grads_exist_at }
   <|>
   do { mk_const `and.intro >>= apply, solve1 prove_grads_exist_at, solve1 prove_grads_exist_at }
   <|>
   do { dsimp,
        -- This is a hack. dget_dinsert is too expensive.
        try $ mk_const `certigrad.mvn_iso_kl_pre >>= rewrite_core semireducible tt tt occurrences.all ff >> dunfold [`dvec.head2],
        try $ mk_const `certigrad.env.get_insert_diff >>= rewrite_core reducible tt tt occurrences.all ff >> swap >> dec_triv,
        try $ mk_const `certigrad.env.get_insert_diff >>= rewrite_core reducible tt tt occurrences.all ff >> swap >> dec_triv,
        try $ mk_const `certigrad.env.get_insert_same >>= rewrite_core reducible tt tt occurrences.all ff,
        try $ mk_const `certigrad.env.get_insert_same >>= rewrite_core reducible tt tt occurrences.all ff,
        try $ mk_const `certigrad.env.get_insert_same >>= rewrite_core reducible tt tt occurrences.all ff,
        (
        (to_expr ``(certigrad.T.nneg_of_pos certigrad.T.exp_pos) >>= exact)
        <|>
        (to_expr ``(certigrad.T.sqrt_pos) >>= apply >> to_expr ``(certigrad.T.exp_pos) >>= exact)
        <|>
        (to_expr ``(certigrad.T.sigmoid_pos) >>= exact)
        <|>
        (to_expr ``(certigrad.T.sigmoid_lt1) >>= exact)
        <|>
        (to_expr ``(certigrad.T.one_plus_pos certigrad.T.exp_pos) >>= exact)
        <|>
        (trace "\n\n\nFAILED: " >> trace_state >> failed))}

meta def prove_pdfs_exist_at : tactic unit :=
do triv
   <|>
   do { mk_const `and.intro >>= apply, solve1 prove_pdfs_exist_at, intro1, solve1 prove_pdfs_exist_at }
   <|>
   do { dsimp,
        -- This is a hack. dget_dinsert is too expensive.
        try $ mk_const `certigrad.mvn_iso_pre >>= rewrite_core semireducible tt tt occurrences.all ff >> dunfold [`dvec.head2],
        try $ mk_const `certigrad.env.get_insert_diff >>= rewrite_core reducible tt tt occurrences.all ff >> swap >> dec_triv,
        try $ mk_const `certigrad.env.get_insert_diff >>= rewrite_core reducible tt tt occurrences.all ff >> swap >> dec_triv,
        try $ mk_const `certigrad.env.get_insert_same >>= rewrite_core reducible tt tt occurrences.all ff,
        try $ mk_const `certigrad.env.get_insert_same >>= rewrite_core reducible tt tt occurrences.all ff,
        try $ mk_const `certigrad.env.get_insert_same >>= rewrite_core reducible tt tt occurrences.all ff,
        (to_expr ``(certigrad.T.sqrt_pos certigrad.T.exp_pos) >>= exact) }

meta def prove_all_costs_scalars : tactic unit :=
triv
<|>
dec_triv
<|>
(applyc `and.intro >> focus [prove_all_costs_scalars, prove_all_costs_scalars])

meta def whnf_rhs_semi : tactic unit :=
do tgt ← target,
   e ← tactic.whnf (expr.app_arg tgt) semireducible,
   change (expr.app (expr.app_fn tgt) e)

meta def cheat_pis : tactic unit :=
(applyc `and.intro >> any_goals (cheat_pis)) <|> (target >>= (λ tgt, if expr.is_pi tgt then mk_sorry >>= exact else skip))

end tactic
