/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certified graph transformation that "reparameterizes" a specific occurrence of a stochastic choice.
-/
import library_dev_extras.util .tensor .tfacts .compute_grad .graph .tactics .predicates .lemmas .env

namespace certigrad
open list

section algebra
open T

lemma mvn_iso_transform {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
  mvn_iso_pdf μ σ x = (prod σ⁻¹) * mvn_iso_pdf 0 1 ((x - μ) / σ) :=
calc  mvn_iso_pdf μ σ x
    = prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) : rfl
... = prod ((sqrt (2 * pi shape) * σ)⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) : by rw [sqrt_mul, sqrt_square]
... = prod (((sqrt (2 * pi shape))⁻¹ * σ⁻¹) * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) : by rw [T.mul_inv_pos (sqrt_pos two_pi_pos) H_σ]
... = (prod σ⁻¹) * prod ((sqrt (2 * pi shape))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) : by simp [prod_mul]
... = (prod σ⁻¹) * prod ((sqrt ((2 * pi shape) * square 1))⁻¹ * exp ((- 2⁻¹) * (square ((((x - μ) / σ) - 0) / 1)))) : by simp [T.div_one, square]
... = (prod σ⁻¹) * mvn_iso_pdf 0 1 ((x - μ) / σ) : rfl

end algebra

open sprog

lemma mvn_reparam_same {shape oshape : S} {μ σ : T shape} (f : dvec T [shape] → T oshape) : σ > 0 →
E (prim (rand.op.mvn_iso shape) ⟦μ, σ⟧) f
=
E (bind (prim (rand.op.mvn_iso_std shape) ⟦⟧) (λ (x : dvec T [shape]), ret ⟦(x^.head * σ) + μ⟧)) f :=
assume (H_σ_pos : σ > 0),
begin
simp only [E.E_bind, E.E_ret],
dunfold E rand.op.mvn_iso rand.op.pdf T.dintegral dvec.head rand.pdf.mvn_iso rand.pdf.mvn_iso_std,
simp only [λ x, mvn_iso_transform μ σ x H_σ_pos],

assert H : ∀ (x : T shape), ((σ * x + μ + -μ) / σ) = x,
  { intro x, simp only [add_assoc, add_neg_self, add_zero], rw mul_comm, rw -T.mul_div_mul_alt, rw T.div_self H_σ_pos, rw mul_one},
definev g : T shape → T oshape := λ (x : T shape), T.mvn_iso_pdf 0 1 ((x - μ) / σ) ⬝ f ⟦x⟧,
assert H_rhs : ∀ (x : T shape), T.mvn_iso_pdf 0 1 x ⬝ f ⟦x * σ + μ⟧ = g (σ * x + μ),
{ intro x, dsimp, rw H, simp },

rw funext H_rhs,
rw T.integral_scale_shift_var g,
dsimp,
simp [T.smul_group]
end

def reparameterize_pre (eshape : S) : list node → env → Prop
| [] inputs := true
| (⟨⟨ref, shape⟩, [⟨μ, .(shape)⟩, ⟨σ, .(shape)⟩], operator.rand (rand.op.mvn_iso .(shape))⟩::nodes) inputs :=
  eshape = shape ∧ σ ≠ μ ∧ env.get (σ, shape) inputs > 0
| (⟨ref, parents, operator.det op⟩::nodes) inputs := reparameterize_pre nodes (env.insert ref (op^.f (env.get_ks parents inputs)) inputs)
| (⟨ref, parents, operator.rand op⟩::nodes) inputs := ∀ x, reparameterize_pre nodes (env.insert ref x inputs)

def reparameterize (fname : ID) : list node → list node
| [] := []

| (⟨⟨ident, shape⟩, [⟨μ, .(shape)⟩, ⟨σ, .(shape)⟩], operator.rand (rand.op.mvn_iso .(shape))⟩::nodes) :=

 (⟨(fname, shape), [],                                       operator.rand (rand.op.mvn_iso_std shape)⟩
::⟨(ident, shape),   [(fname, shape), (σ, shape), (μ, shape)], operator.det (det.op.special (det.special.mul_add shape))⟩
::nodes)

| (n::nodes) := n :: reparameterize nodes

theorem reparameterize_correct (costs : list ID) :
∀ (nodes : list node) (inputs : env) (fref : reference),
  reparameterize_pre fref.2 nodes inputs →
  nodup (env.keys inputs ++ map node.ref nodes) →
  all_parents_in_env inputs nodes →
  (fref ∉ env.keys inputs ++ map node.ref nodes) →
  (fref.1 ∉ costs) →
E (graph.to_dist (λ env₀, ⟦sum_costs env₀ costs⟧) inputs (reparameterize fref.1 nodes)) dvec.head
=
E (graph.to_dist (λ env₀, ⟦sum_costs env₀ costs⟧) inputs nodes) dvec.head

| [] _ _ _ _ _ _ _ := rfl

| (⟨⟨ident, shape⟩, [⟨μ, .(shape)⟩, ⟨σ, .(shape)⟩], operator.rand (rand.op.mvn_iso .(shape))⟩::nodes) inputs fref H_pre H_nodup H_ps_in_env H_fresh H_not_cost :=
begin
dunfold reparameterize,
assertv H_eshape : fref.2 = shape := H_pre^.left,
assert H_fref : fref = (fref.1, shape),
{ clear reparameterize_correct, cases fref with fref₁ fref₂, dsimp at H_eshape, rw H_eshape },

assertv H_σ_μ : σ ≠ μ := H_pre^.right^.left,

dunfold graph.to_dist operator.to_dist,
dsimp,
simp [E.E_bind],
erw (mvn_reparam_same _ H_pre^.right^.right),
simp [E.E_bind, E.E_ret],
dunfold dvec.head,
dsimp,
apply congr_arg, apply funext, intro x,

note H_nodup₀ := H_nodup,
note H_fresh₀ := H_fresh,

assertv H_μ_mem : (μ, shape) ∈ env.keys inputs := env.has_key_mem_keys (H_ps_in_env^.left (μ, shape) (mem_cons_self _ _)),
assertv H_σ_mem : (σ, shape) ∈ env.keys inputs := env.has_key_mem_keys (H_ps_in_env^.left (σ, shape) (mem_cons_of_mem _ (mem_cons_self _ _))),
assertv H_ident_mem : (ident, shape) ∈ (ident, shape) :: map node.ref nodes:= mem_of_cons_same,

assertv H_μ_neq_ident : (μ, shape) ≠ (ident, shape) := nodup_append_neq H_μ_mem H_ident_mem H_nodup,
assertv H_σ_neq_ident : (σ, shape) ≠ (ident, shape) := nodup_append_neq H_σ_mem H_ident_mem H_nodup,

assertv H_fref_notmem₁ : (fref.1, shape) ∉ env.keys inputs := eq.rec_on H_fref (not_mem_of_not_mem_append_left H_fresh),
assertv H_fref_notmem₂ : (fref.1, shape) ∉ (ident, shape) :: map node.ref nodes := eq.rec_on H_fref (not_mem_of_not_mem_append_right H_fresh),

assertv H_μ_neq_fref : (μ, shape) ≠ (fref.1, shape) := mem_not_mem_neq H_μ_mem H_fref_notmem₁,
assertv H_σ__neq_fref : (σ, shape) ≠ (fref.1, shape) := mem_not_mem_neq H_σ_mem H_fref_notmem₁,
assertv H_ident_neq_fref : (ident, shape) ≠ (fref.1, shape) := mem_not_mem_neq H_ident_mem H_fref_notmem₂,

dunfold env.get_ks,
tactic.dget_dinsert,

rw (env.insert_insert_flip _ _ _ H_ident_neq_fref),
dsimp,

definev fval : T shape := dvec.head x,
definev fval_inputs : env := env.insert (ident, shape)
                                        (det.op.f (det.op.special (det.special.mul_add shape))
                                                  ⟦dvec.head x, (env.get (σ, shape) inputs : T shape), (env.get (μ, shape) inputs : T shape)⟧)
                                         inputs,

assertv H_ps_in_env_next : all_parents_in_env fval_inputs nodes := H_ps_in_env^. right _,
assertv H_fresh_next : (fref.1, shape) ∉ env.keys fval_inputs ++ map node.ref nodes := eq.rec_on H_fref (env.not_mem_of_insert H_fresh₀),
erw (@to_dist_congr_insert costs nodes fval_inputs (fref.1, shape) fval H_ps_in_env_next H_fresh_next H_not_cost),
dsimp,
dunfold det.op.f,
rw [add_comm, mul_comm],
reflexivity
end

| (⟨(ref, shape), [], operator.det op⟩::nodes) inputs fref H_pre H_nodup H_ps_in_env H_fresh H_not_cost :=
begin
dunfold reparameterize graph.to_dist operator.to_dist,
simp [E.E_bind, E.E_ret],
definev x : T shape := op^.f (env.get_ks [] inputs),
assertv H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (ref, shape) x inputs) nodes := H_ps_in_env^.right _,
assertv H_fresh_next : fref ∉ env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes := env.not_mem_of_insert H_fresh,
apply (reparameterize_correct _ _ fref H_pre_next H_nodup_next H_ps_in_env_next H_fresh_next H_not_cost)
end

| (⟨(ref, shape), [], operator.rand op⟩::nodes) inputs fref H_pre H_nodup H_ps_in_env H_fresh H_not_cost :=
begin
dunfold reparameterize graph.to_dist,
simp [E.E_bind],
apply congr_arg, apply funext, intro x,
assertv H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) (dvec.head x) inputs) := by apply H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (ref, shape) (dvec.head x) inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (ref, shape) (dvec.head x) inputs) nodes := H_ps_in_env^.right x^.head,
assertv H_fresh_next : fref ∉ env.keys (env.insert (ref, shape) (dvec.head x) inputs) ++ map node.ref nodes := env.not_mem_of_insert H_fresh,
apply (reparameterize_correct _ _ fref H_pre_next H_nodup_next H_ps_in_env_next H_fresh_next H_not_cost)
end

| (⟨(ref, shape), [(parent₁, shape₁)], operator.det op⟩::nodes) inputs fref H_pre H_nodup H_ps_in_env H_fresh H_not_cost :=
begin
dunfold reparameterize graph.to_dist operator.to_dist,
simp [E.E_bind, E.E_ret],
definev x : T shape := det.op.f op (env.get_ks [(parent₁, shape₁)] inputs),
assertv H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (ref, shape) x inputs) nodes := H_ps_in_env^.right x,
assertv H_fresh_next : fref ∉ env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes := env.not_mem_of_insert H_fresh,
apply (reparameterize_correct _ _ fref H_pre_next H_nodup_next H_ps_in_env_next H_fresh_next H_not_cost)
end

| (⟨(ref, shape), [(parent₁, shape₁), (parent₂, shape₂)], operator.det op⟩::nodes) inputs fref H_pre H_nodup H_ps_in_env H_fresh H_not_cost :=
begin
dunfold reparameterize graph.to_dist operator.to_dist,
simp [E.E_bind, E.E_ret],
definev x : T shape := det.op.f op (env.get_ks [(parent₁, shape₁), (parent₂, shape₂)] inputs),
assertv H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (ref, shape) x inputs) nodes := H_ps_in_env^.right x,
assertv H_fresh_next : fref ∉ env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes := env.not_mem_of_insert H_fresh,
apply (reparameterize_correct _ _ fref H_pre_next H_nodup_next H_ps_in_env_next H_fresh_next H_not_cost)
end

| (⟨(ref, shape), (parent₁, shape₁) :: (parent₂, shape₂) :: (parent₃, shape₃) :: parents, operator.det op⟩::nodes) inputs fref H_pre H_nodup H_ps_in_env H_fresh H_not_cost :=
begin
dunfold reparameterize graph.to_dist operator.to_dist,
simp [E.E_bind, E.E_ret],
definev x : T shape := det.op.f op (env.get_ks ((parent₁, shape₁) :: (parent₂, shape₂) :: (parent₃, shape₃) :: parents) inputs),
assertv H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (ref, shape) x inputs) nodes := H_ps_in_env^.right x,
assertv H_fresh_next : fref ∉ env.keys (env.insert (ref, shape) x inputs) ++ map node.ref nodes := env.not_mem_of_insert H_fresh,
apply (reparameterize_correct _ _ fref H_pre_next H_nodup_next H_ps_in_env_next H_fresh_next H_not_cost)
end

def reparam : graph → graph
| g := ⟨reparameterize (ID.str label.ε) g^.nodes, g^.costs, g^.targets, g^.inputs⟩

end certigrad
