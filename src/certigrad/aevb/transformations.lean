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

lemma integrate_kl_sound (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₀ : graph := graph_naive a x_data, fdict : env := mk_input_dict ws g₀ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₀^.targets idx tgt) (θ : T tgt.2),
E (graph.to_dist (λ m, ⟦sum_costs m (integrate_kl g₀)^.costs⟧) (env.insert tgt θ fdict) (integrate_kl g₀)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g₀^.costs⟧) (env.insert tgt θ fdict) g₀^.nodes) dvec.head := sorry
/-
by do whnf_target,
      [tgt, idx, H_at_idx, θ] ← intros | failed,
      forall_idxs prove_model_base (do
         to_expr ```(integrate_mvn_iso_kl_correct (ID.str label.encoding_loss) [ID.str label.decoding_loss] (graph_naive a x_data)^.nodes) >>= apply,
         all_goals (cgsimp >> try prove_is_mvn_integrable >> try T.prove_preconditions)) idx
-/

lemma reparam_sound (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₁ : graph := integrate_kl (graph_naive a x_data), fdict : env := mk_input_dict ws g₁ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₁^.targets idx tgt) (θ : T tgt.2),
E (graph.to_dist (λ m, ⟦sum_costs m (reparam g₁)^.costs⟧) (env.insert tgt θ fdict) (reparam g₁)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g₁^.costs⟧) (env.insert tgt θ fdict) g₁^.nodes) dvec.head := sorry
/-
by do whnf_target,
      [tgt, idx, H_at_idx, θ] ← intros | failed,
      forall_idxs prove_model_base (do
         to_expr ```(reparameterize_correct _ (integrate_kl $ graph_naive a x_data)^.nodes _ (ID.str label.ε, [a^.nz, a^.bs])) >>= apply,
         all_goals cgsimp) idx
-/

-- TODO(dhs): this is annoying, rw and simp should whnf the let
lemma aevb_transformations_sound {a : arch} (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g₀ : graph := naive_aevb a x_data, g_aevb : graph := reparam (integrate_kl g₀), fdict : env := mk_input_dict ws g₀ in
∀ (tgt : reference) (idx : ℕ) (H_at_idx : at_idx g₀^.targets idx tgt) (θ : T tgt.2),
E (graph.to_dist (λ m, ⟦sum_costs m g₀^.costs⟧) (env.insert tgt θ fdict) g₀^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g_aevb^.costs⟧) (env.insert tgt θ fdict) g_aevb^.nodes) dvec.head :=
begin
whnf_target,
intros tgt idx H_at_idx θ,
note H₁ := @reparam_sound a ws x_data tgt idx,
note H₂ := @integrate_kl_sound a ws x_data tgt idx,
dsimp at *,
simp only [naive_aevb_as_graph] at *,
erw [H₁, H₂],
all_goals { assumption }
end

end aevb
end certigrad
