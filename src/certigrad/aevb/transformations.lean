/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proofs that integrating out the KL and reparametizing are sound when
applied to the naive variational encoder.
-/
import .util .naive ..prove_model_ok

namespace certigrad
namespace aevb

open graph list tactic certigrad.tactic

lemma integrate_kl_sound (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g : graph   := graph_naive a x_data, fdict : env := mk_input_dict ws g in
E (graph.to_dist (λ m, ⟦sum_costs m (integrate_kl g)^.costs⟧) fdict (integrate_kl g)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) fdict g^.nodes) dvec.head :=
let g : graph   := graph_naive a x_data, fdict : env := mk_input_dict ws g in
begin
apply integrate_mvn_iso_kl_correct label.encoding_loss [label.decoding_loss] g^.nodes fdict,
all_goals { cgsimp }
end

lemma reparam_sound (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g : graph   := integrate_kl $ graph_naive a x_data, fdict : env := mk_input_dict ws g in
E (graph.to_dist (λ m, ⟦sum_costs m (reparam g)^.costs⟧) fdict (reparam g)^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) fdict g^.nodes) dvec.head :=
let g : graph   := integrate_kl $ graph_naive a x_data, fdict : env := mk_input_dict ws g in
begin
apply reparameterize_correct g^.costs g^.nodes fdict (ID.str label.ε, [a^.nz, a^.bs]),
all_goals { cgsimp }
end

-- TODO(dhs): this is annoying, rw and simp should whnf the let
lemma aevb_correct {a : arch} (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
let g : graph := graph_naive a x_data, g_aevb : graph := reparam (integrate_kl g), fdict : env := mk_input_dict ws g in
E (graph.to_dist (λ m, ⟦sum_costs m g_aevb^.costs⟧) fdict g_aevb^.nodes) dvec.head
=
E (graph.to_dist (λ m, ⟦sum_costs m g^.costs⟧) fdict g^.nodes) dvec.head :=
begin
note H₁ := reparam_sound, note H₂ := integrate_kl_sound,
dsimp at H₁, dsimp at H₂,
dsimp,
erw [H₁, H₂]
end

end aevb
end certigrad
