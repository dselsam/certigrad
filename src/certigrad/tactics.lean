/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous tactics.
-/
import .util

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
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core reducible s tac r e,
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
  assumption <|> (mk_const `pair_neq_of_neq₁ >>= apply >> assumption)

meta def dget_dinsert : tactic unit := do
  s ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.env.get_insert_same >>= flip simp_lemmas.add_simp `certigrad.env.get_insert_diff,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core reducible s refs_neq r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

meta def dget_dinsert_at (n : name) : tactic unit := do
  s ← simp_lemmas.add_simp simp_lemmas.mk `certigrad.env.get_insert_same >>= flip simp_lemmas.add_simp `certigrad.env.get_insert_diff,
  at_hyp n (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core reducible s refs_neq r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))

run_cmd mk_simp_attr `natne

attribute [natne] nat.bit0_inj_eq nat.bit1_inj_eq nat.zero_ne_bit0_eq nat.bit0_ne_zero_eq nat.one_ne_bit1_eq nat.bit1_ne_one_eq
                  nat.bit1_ne_bit0_eq nat.bit0_ne_bit1_eq nat.bit0_inj_eq nat.bit1_inj_eq nat.zero_ne_one_eq nat.one_ne_zero_eq
                  nat.zero_ne_bit1_eq nat.bit1_ne_zero_eq nat.one_ne_bit0_eq nat.bit0_ne_one_eq

meta def prove_nats_neq : tactic unit :=
do s ← join_user_simp_lemmas tt [`natne],
   tgt ← target,
   (new_tgt, pf) ← simplify s tgt,
   replace_target new_tgt pf,
   triv

end tactic
