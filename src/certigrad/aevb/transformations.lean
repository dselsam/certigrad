/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proofs that integrating out the KL and reparametizing are sound when
applied to the naive variational encoder.
-/
import .util .prog .graph ..prove_model_ok ..kl

namespace certigrad
namespace aevb

open graph list tactic certigrad.tactic

meta def prove_transformation (e : pexpr) :=
do whnf_target,
  [tgt, idx, H_at_idx, θ] ← intro_lst [`tgt, `idx, `H_at_idx, `θ] | failed,
  forall_idxs prove_model_base
              (do H_at_idx ← get_local `H_at_idx,
                  mk_app `and.right [H_at_idx] >>= note `H_tgt_eq,
                  H_tgt_eq_type ← get_local `H_tgt_eq >>= infer_type,
                  s ← join_user_simp_lemmas true [`cgsimp],
                  (H_tgt_eq_new_type, pr) ← simplify s H_tgt_eq_type {},
                  get_local `H_tgt_eq >>= λ H_tgt_eq, replace_hyp H_tgt_eq H_tgt_eq_new_type pr,
                  get_local `H_tgt_eq >>= subst,
                  to_expr e >>= apply,
                  all_goals (cgsimp >> try prove_is_mvn_integrable >> try T.prove_preconditions))
              idx

#print "proving integrate_kl_sound..."
lemma integrate_kl_sound (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₀ : graph := graph_naive a x_data, fdict : env := mk_input_dict ws g₀ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₀^.targets idx tgt) (θ : T tgt.2),
E (graph.to_dist (λ m, ⟦sum_costs m (integrate_kl g₀)^.costs⟧) (env.insert tgt θ fdict) (integrate_kl g₀)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g₀^.costs⟧) (env.insert tgt θ fdict) g₀^.nodes) dvec.head :=
by prove_transformation ```(integrate_mvn_iso_kl_correct (ID.str label.encoding_loss) [ID.str label.decoding_loss] (graph_naive a x_data)^.nodes)

#print "proving reparam_sound..."
lemma reparam_sound (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₁ : graph := integrate_kl (graph_naive a x_data), fdict : env := mk_input_dict ws g₁ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₁^.targets idx tgt) (θ : T tgt.2),
E (graph.to_dist (λ m, ⟦sum_costs m (reparam g₁)^.costs⟧) (env.insert tgt θ fdict) (reparam g₁)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g₁^.costs⟧) (env.insert tgt θ fdict) g₁^.nodes) dvec.head :=
by prove_transformation ```(reparameterize_correct [ID.str label.encoding_loss, ID.str label.decoding_loss]
                                                   (integrate_kl $ graph_naive a x_data)^.nodes _ (ID.str label.ε, [a^.nz, a^.bs]))

#print "proving aevb_transformations_sound..."

lemma aevb_transformations_sound {a : arch} (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₀ : graph := naive_aevb a x_data, g_aevb : graph := reparam (integrate_kl g₀), fdict : env := mk_input_dict ws g₀ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₀^.targets idx tgt) (θ : T tgt.2),
E (graph.to_dist (λ m, ⟦sum_costs m g₀^.costs⟧) (env.insert tgt θ fdict) g₀^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g_aevb^.costs⟧) (env.insert tgt θ fdict) g_aevb^.nodes) dvec.head :=

begin
whnf_target,
intros tgt idx H_at_idx θ,
-- TODO(dhs): this is annoying, rw and simp should whnf the let
note H₁ := @reparam_sound a ws x_data tgt idx,
note H₂ := @integrate_kl_sound a ws x_data tgt idx,
simp only [naive_aevb_as_graph] at *,
erw [H₁, H₂],
all_goals { assumption }
end

end aevb
end certigrad
