/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic computation graphs.
-/
import .det .rand library_dev_extras.util .id .sprog .env .reference

namespace certigrad

inductive operator (ishapes : list S) (oshape : S) : Type
| det : det.op ishapes oshape → operator
| rand : rand.op ishapes oshape → operator

namespace operator

def to_dist (m : env) : Π {parents : list reference} {oshape : S}, operator parents^.p2 oshape → sprog [oshape]
| parents _ (det op)   := sprog.ret ⟦op^.f (env.get_ks parents m)⟧
| parents _ (rand op) := sprog.prim op (env.get_ks parents m)

end operator

structure node : Type := (ref : reference) (parents : list (ID × S)) (op : operator parents^.p2 ref.2)
structure graph : Type := (nodes : list node) (costs : list ID) (targets inputs : list reference)

namespace graph

open sprog

def to_dist {fshapes : list S} (k : env → dvec T fshapes) : env → list node → sprog fshapes
| m []            := ret (k m)
| m (⟨ref, parents, op⟩::nodes) := bind (operator.to_dist m op)
                                        (λ (x : dvec T [ref.2]), to_dist (env.insert ref x^.head m) nodes)

open list

lemma envs_match_helper {fshapes : list S} (k₁ k₂ : env → dvec T fshapes) : Π (inputs : env) (nodes : list node),
    ∀ (ref : reference) (x : T ref.2),
      nodup (env.keys inputs ++ (ref :: map node.ref nodes)) →
      (∀ (m : env), (∀ (ref : reference), env.has_key ref inputs → env.get ref m = env.get ref inputs) → k₁ m = k₂ m) →
      ∀  (m : env),
         (∀ (r : reference), env.has_key r (env.insert ref x inputs) → env.get r m = env.get r (env.insert ref x inputs)) → k₁ m = k₂ m :=
assume inputs nodes ref x H_nodup H_k_eq,
assume (m : env) H_next_envs_agree,
  have H_envs_agree : ∀ (ref' : reference), env.has_key ref' inputs → env.get ref' m = env.get ref' inputs, from
    assume (ref' : reference) (H_inputs_contains_ref' : env.has_key ref' inputs),
    show env.get ref' m = env.get ref' inputs, from
    have H_next_contains_name : env.has_key ref' (env.insert ref x inputs), from env.has_key_insert H_inputs_contains_ref',
    have H_next_agree : env.get ref' m = env.get ref' (env.insert ref x inputs), from H_next_envs_agree _ H_next_contains_name,
    have H_ref'_neq_ref : ref' ≠ ref, from
      have H_ref'_in_keys : ref' ∈ env.keys inputs, from env.has_key_mem_keys H_inputs_contains_ref',
      have H_ref_in_rest : ref ∈ ref :: map node.ref nodes, from mem_of_cons_same,
      nodup_append_neq H_ref'_in_keys H_ref_in_rest H_nodup,
    begin rw env.get_insert_diff _ _ H_ref'_neq_ref at H_next_agree, exact H_next_agree end,
  H_k_eq _ H_envs_agree

lemma to_dist_congr {fshapes : list S} (k₁ k₂ : env → dvec T fshapes) : Π (inputs : env) (nodes : list node),
      nodup (env.keys inputs ++ map node.ref nodes) →
      (∀ (m : env), (∀ (ref : reference), env.has_key ref inputs → env.get ref m = env.get ref inputs) → k₁ m = k₂ m) →
      to_dist k₁ inputs nodes = to_dist k₂ inputs nodes

-- Case 1
| inputs [] H_nodup H_k_eq :=
show to_dist k₁ inputs [] = to_dist k₂ inputs [], from
show sprog.ret (k₁ inputs) = sprog.ret (k₂ inputs), from
have H_inputs_eq : ∀ (ref : reference), env.has_key ref inputs → env.get ref inputs = env.get ref inputs, from
  assume (ref : reference) (H_inputs_contain : env.has_key ref inputs), rfl,
by rw (H_k_eq _ H_inputs_eq)

-- Case 2
| inputs (⟨ref, parents, op⟩::nodes) H_nodup H_k_eq :=
show to_dist k₁ inputs (⟨ref, parents, op⟩ :: nodes) = to_dist k₂ inputs (⟨ref, parents, op⟩ :: nodes), from
show bind (operator.to_dist inputs op) (λ (x : dvec T [ref.2]), to_dist k₁ (env.insert ref x^.head inputs) nodes)
     =
     bind (operator.to_dist inputs op) (λ (x : dvec T [ref.2]), to_dist k₂ (env.insert ref x^.head inputs) nodes), from
suffices ∀ (x : dvec T [ref.2]), to_dist k₁ (env.insert ref x^.head inputs) nodes = to_dist k₂ (env.insert ref x^.head inputs) nodes, from
  congr_arg _ (funext this),
assume (x : dvec T [ref.2]),
show to_dist k₁ (env.insert ref x^.head inputs) nodes = to_dist k₂ (env.insert ref x^.head inputs) nodes, from
have H_next_nodup : nodup (env.keys (env.insert ref x^.head inputs) ++ map node.ref nodes), from
  env.nodup_insert H_nodup,
to_dist_congr _ _ H_next_nodup (envs_match_helper k₁ k₂ _ _ _ _ H_nodup H_k_eq)

lemma graph_to_dist_inputs_congr {fshapes : list S} (k : env → dvec T fshapes) (inputs₁ inputs₂ : env) (nodes : list node) :
  inputs₁ = inputs₂ → graph.to_dist k inputs₁ nodes = graph.to_dist k inputs₂ nodes := assume H, by rw H

end graph

noncomputable def is_gintegrable {shapes : list S} (k : env → dvec T shapes) {shape : S} : Π (m : env) (nodes : list node) (f : dvec T shapes → T shape), Prop
| _ [] f := true

| m (⟨ref, parents, operator.det op⟩ :: nodes) f := is_gintegrable (env.insert ref (op^.f (env.get_ks parents m)) m) nodes f

| m (⟨ref, parents, operator.rand op⟩ :: nodes) f :=
  let m' := (λ (y : T ref.2), env.insert ref y m) in
  T.is_integrable (λ x, op^.pdf (env.get_ks parents m) x ⬝ E (graph.to_dist k (m' x) nodes) f) ∧
  ∀ x, is_gintegrable (m' x) nodes f

open list

noncomputable def is_gdifferentiable (k : env → dvec T [[]]) : Π (tgt : reference) (m : env) (nodes : list node) (f : dvec T [[]] → ℝ), Prop
| tgt _ [] f := true

| tgt m (⟨ref, parents, operator.det op⟩ :: nodes) f :=
let θ := env.get tgt m,
    x := op^.f (env.get_ks parents m),
    g := (λ (v : dvec T parents^.p2) (θ : T tgt.2), E (graph.to_dist k (env.insert ref (det.op.f op v) (env.insert tgt θ m)) nodes) dvec.head) in

T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), g (env.get_ks parents (env.insert tgt θ m)) θ₀) θ
∧ T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), sumr (map (λ (idx : ℕ), g (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ)
                                                       (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))) θ
∧ is_gdifferentiable tgt (env.insert ref x m) nodes f
∧ ∀ {idx : ℕ}, idx ∈ riota (length parents) → tgt = dnth parents idx → is_gdifferentiable ref (env.insert ref x m) nodes f

| tgt m (⟨ref, parents, operator.rand op⟩ :: nodes) f :=
let g : dvec T [ref.2] → T tgt.2 → ℝ :=
           (λ (x : dvec T [ref.2]) (θ₀ : T tgt.2), E (graph.to_dist k (env.insert ref x^.head (env.insert tgt θ₀ m)) nodes) dvec.head),
   θ : T tgt.2 := env.get tgt m,
   m' := (λ (y : T ref.2), env.insert ref y m) in

T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), E (sprog.prim op (env.get_ks parents (env.insert tgt θ m))) (λ (y : dvec T [ref.snd]), g y θ₀)) θ
∧ T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)), sumr (map (λ (idx : ℕ), E (sprog.prim op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx))
                                                                       (λ (y : dvec T [ref.snd]), g y θ))
                                                       (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents))))) θ
∧ ∀ (y : T ref.2), is_gdifferentiable tgt (env.insert ref y m) nodes f

lemma is_gintegrable_k_congr {fshapes : list S} {fshape : S} (k₁ k₂ : env → dvec T fshapes) : Π (inputs : env) (nodes : list node) (f : dvec T fshapes → T fshape),
  nodup (env.keys inputs ++ map node.ref nodes) →
  (∀ (m : env), (∀ (ref : reference), env.has_key ref inputs → env.get ref m = env.get ref inputs) → k₁ m = k₂ m) →
  is_gintegrable k₁ inputs nodes f → is_gintegrable k₂ inputs nodes f

| inputs [] f H_nodup H_k_eq H_gint₁ := trivial

| inputs (⟨ref, parents, operator.det op⟩ :: nodes) f H_nodup H_k_eq H_gint₁ :=
begin
dsimp [is_gintegrable] at H_gint₁,
dsimp [is_gintegrable],
apply is_gintegrable_k_congr _ _ _ (env.nodup_insert H_nodup) (graph.envs_match_helper k₁ k₂ _ _ _ _ H_nodup H_k_eq) H_gint₁
end

| inputs (⟨ref, parents, operator.rand op⟩ :: nodes) f H_nodup H_k_eq H_gint₁ :=
begin
dsimp [is_gintegrable] at H_gint₁,
dsimp [is_gintegrable],
split,
{
assertv H_dist_congr : ∀ x, graph.to_dist k₁ (env.insert ref x inputs) nodes = graph.to_dist k₂ (env.insert ref x inputs) nodes :=
assume x,
graph.to_dist_congr k₁ k₂ _ _ (env.nodup_insert H_nodup) (graph.envs_match_helper k₁ k₂ _ _ _ _ H_nodup H_k_eq),
simp only [H_dist_congr] at H_gint₁,
exact H_gint₁^.left
},

{
intro x,
dsimp [is_gintegrable] at H_gint₁,
dsimp [is_gintegrable],
apply is_gintegrable_k_congr _ _ _ (env.nodup_insert H_nodup) (graph.envs_match_helper k₁ k₂ _ _ _ _ H_nodup H_k_eq) (H_gint₁^.right x)
}

end

-- TODO(dhs): this seems like it could be provable given is_gintegrable and compute_grad_slow_correct
noncomputable def is_nabla_gintegrable (k : env → dvec T [[]]) : Π (tgt : reference) (m : env) (nodes : list node) (f : dvec T [[]] → ℝ), Prop
| tgt m [] f := true

| tgt m (⟨ref, parents, operator.det op⟩ :: nodes) f :=
  is_nabla_gintegrable tgt (env.insert ref (op^.f (env.get_ks parents m)) m) nodes f
  ∧ ∀ {idx : ℕ}, idx ∈ riota (length parents) → tgt = dnth parents idx → is_nabla_gintegrable ref (env.insert ref (op^.f (env.get_ks parents m)) m) nodes f

| tgt m (⟨ref, parents, operator.rand op⟩ :: nodes) f :=
  T.is_integrable (λ (x : T ref.2), op^.pdf (env.get_ks parents m) x ⬝ ∇ (λ (θ₀ : T tgt.2), E (graph.to_dist k (env.insert ref x (env.insert tgt θ₀ m)) nodes) f) (env.get tgt m))

∧ T.is_integrable
    (λ (x : T (ref.snd)),
       rand.op.pdf op (env.get_ks parents m) x ⬝ sumr
         (map
            (λ (idx : ℕ),
               E
                 (graph.to_dist k
                    (env.insert ref x m)
                    nodes)
                 dvec.head ⬝ ∇
                 (λ (θ₀ : T (tgt.snd)),
                    T.log (rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents m) idx) x))
                 (env.get tgt m))
            (filter (λ (idx : ℕ), tgt = dnth parents idx) (riota (length parents)))))

  ∧ ∀ (y : T ref.2), is_nabla_gintegrable tgt (env.insert ref y m) nodes f

--  is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m tgt⟧) inputs nodes dvec.head →

end certigrad
