/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certified graph transformation that integrates out a specific KL divergence term.
-/
import library_dev_extras.util .tensor .compute_grad .graph .tactics .predicates .lemmas .env .expected_value

namespace certigrad
open list

def integrate_mvn_iso_kl (eloss : ID) : list node → list node
| [] := []

| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
 ::⟨(el, []), [(μ', .(shape')), (σ', .(shape')), (z', .(shape'))], operator.det (det.op.mvn_iso_empirical_kl shape')⟩
 ::nodes) :=
 (⟨(el, []), [⟨μ, shape⟩, ⟨σ, shape⟩], operator.det (det.op.special (det.special.mvn_iso_kl shape))⟩
::⟨(z, shape), [⟨μ, shape⟩, ⟨σ, shape⟩], operator.rand (rand.op.mvn_iso shape)⟩
::nodes)

| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩ ::nodes) :=
⟨(z, shape), [(μ, shape), (σ, shape)], operator.rand (rand.op.mvn_iso shape)⟩ :: integrate_mvn_iso_kl nodes

| (n::nodes) := n :: integrate_mvn_iso_kl nodes

def integrate_mvn_iso_kl_pre (eloss : ID) : list node → env → Prop
-- EQ1
| [] _ := true
-- EQ2 (a)
| (⟨(rname, rshape), [], operator.det op⟩::nodes) inputs :=
integrate_mvn_iso_kl_pre nodes (env.insert (rname, rshape) (op^.f (env.get_ks [] inputs)) inputs)
-- EQ2 (b)
| (⟨(rname, rshape), [], operator.rand op⟩::nodes) inputs := false
-- EQ3 (a)
| (⟨(rname, rshape), [(pname, pshape)], operator.det op⟩::nodes) inputs :=
integrate_mvn_iso_kl_pre nodes (env.insert (rname, rshape) (op^.f (env.get_ks [(pname, pshape)] inputs)) inputs)
-- EQ3 (b)
| (⟨(rname, rshape), [(pname, pshape)], operator.rand op⟩::nodes) inputs := false
-- EQ4
| (⟨(rname, rshape), [(pname₁, pshape₁), (pname₂, pshape₂)], operator.det op⟩::nodes) inputs :=
integrate_mvn_iso_kl_pre nodes (env.insert (rname, rshape) (op^.f (env.get_ks [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs)
-- EQ5
| [⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩] inputs := false
-- EQ6
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [], op⟩::nodes) inputs := false
-- EQ7
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃)], op⟩::nodes) inputs := false
-- EQ8
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄)], op⟩::nodes) inputs := false
-- EQ9
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], operator.det (det.op.special op)⟩::nodes) inputs := false
-- EQ10
| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
 ::⟨(el, []), [(μ', .(shape')), (σ', .(shape')), (z', .(shape'))], operator.det (det.op.mvn_iso_empirical_kl shape')⟩
 ::nodes) inputs :=
(μ = μ' ∧ σ = σ' ∧ z = z' ∧ shape = shape' ∧ eloss = el ∧ σ ≠ μ)
∧ (env.get (σ, shape) inputs > 0 ∧ ∀ (y : T shape), all_parents_in_env (env.insert (z, shape) y inputs) nodes)
-- EQ11
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], operator.rand op⟩::nodes) inputs := false
-- EQ12
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), ((pname₃, shape₃)::(pname₄, shape₄)::(pname₅, shape₅)::parent::parents), op⟩::nodes) inputs := false
-- EQ13
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, (shape₂ :: shapes₂)), parents, op⟩::nodes) inputs := false
-- EQ14 (a)
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), operator.det op⟩::nodes) inputs :=
integrate_mvn_iso_kl_pre nodes (env.insert (rname₂, shape₂) (op^.f $ env.get_ks ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents) inputs) inputs)
-- EQ14 (b)
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), operator.rand op⟩::nodes) inputs := false

theorem integrate_mvn_iso_kl_correct (eloss : ID) (costs : list ID) :
∀ (nodes : list node) (inputs : env),
  eloss ∉ costs →
  integrate_mvn_iso_kl_pre eloss nodes inputs →
  nodup (env.keys inputs ++ map node.ref nodes) →
  all_parents_in_env inputs nodes →
  pdfs_exist_at nodes inputs →
  is_gintegrable (λ m, ⟦sum_costs m (eloss::costs)⟧) inputs (integrate_mvn_iso_kl eloss nodes) dvec.head →
  is_gintegrable (λ m, ⟦sum_costs m (eloss::costs)⟧) inputs nodes dvec.head →
E (graph.to_dist (λ env₀, ⟦sum_costs env₀ (eloss::costs)⟧) inputs (integrate_mvn_iso_kl eloss nodes)) dvec.head
=
E (graph.to_dist (λ env₀, ⟦sum_costs env₀ (eloss::costs)⟧) inputs nodes) dvec.head
-- EQ1
--#check integrate_mvn_iso_kl.equations._eqn_1
| [] _ _ _ _ _ _ _ _ := rfl

-- EQ2 (a)
--#check integrate_mvn_iso_kl.equations._eqn_2
| (⟨(rname, rshape), [], operator.det op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint :=
begin
dunfold graph.to_dist operator.to_dist integrate_mvn_iso_kl,
dunfold integrate_mvn_iso_kl_pre at H_pre,
simp [E.E_bind, E.E_ret],
assertv H_pre_next : integrate_mvn_iso_kl_pre eloss nodes (env.insert (rname, rshape) (op^.f (env.get_ks nil inputs)) inputs) := H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (rname, rshape) (op^.f (env.get_ks nil inputs)) inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (rname, rshape) (op^.f (env.get_ks nil inputs)) inputs) nodes := H_ps_in_env^.right _,
exact (integrate_mvn_iso_kl_correct _ _ H_eloss_not_cost H_pre_next H_nodup_next H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
end

-- EQ2 (b)
| (⟨(rname, rshape), [], operator.rand op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ3 (a)
| (⟨(rname, rshape), [(pname, pshape)], operator.det op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint :=
begin
dunfold graph.to_dist operator.to_dist integrate_mvn_iso_kl,
dunfold integrate_mvn_iso_kl_pre at H_pre,
simp [E.E_bind, E.E_ret],
assertv H_pre_next : integrate_mvn_iso_kl_pre eloss nodes (env.insert (rname, rshape) (op^.f (env.get_ks [(pname, pshape)] inputs)) inputs) := H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (rname, rshape) (op^.f (env.get_ks [(pname, pshape)] inputs)) inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (rname, rshape) (op^.f (env.get_ks [(pname, pshape)] inputs)) inputs) nodes := H_ps_in_env^.right _,
exact (integrate_mvn_iso_kl_correct _ _ H_eloss_not_cost H_pre_next H_nodup_next H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
end

-- EQ3 (b)
| (⟨(rname, rshape), [(pname, pshape)], operator.rand op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ4
| (⟨(rname, rshape), [(pname₁, pshape₁), (pname₂, pshape₂)], operator.det op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint :=
begin
dunfold graph.to_dist operator.to_dist integrate_mvn_iso_kl,
dunfold integrate_mvn_iso_kl_pre at H_pre,
simp [E.E_bind, E.E_ret],
assertv H_pre_next : integrate_mvn_iso_kl_pre eloss nodes (env.insert (rname, rshape) (op^.f (env.get_ks [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs) := H_pre,
assertv H_nodup_next : nodup (env.keys (env.insert (rname, rshape) (op^.f (env.get_ks [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs) ++ map node.ref nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env (env.insert (rname, rshape) (op^.f (env.get_ks [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs) nodes := H_ps_in_env^.right _,
exact (integrate_mvn_iso_kl_correct _ _ H_eloss_not_cost H_pre_next H_nodup_next H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
end

-- EQ5
--#check integrate_mvn_iso_kl.equations._eqn_5
| [⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩] inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ6
--#check integrate_mvn_iso_kl.equations._eqn_6
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [], op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ7
--#check integrate_mvn_iso_kl.equations._eqn_7
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃)], op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ8
--#check integrate_mvn_iso_kl.equations._eqn_8
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄)], op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ9
--#check integrate_mvn_iso_kl.equations._eqn_9
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], operator.det (det.op.special op)⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint :=
false.rec _ H_pre

-- EQ10
--#check integrate_mvn_iso_kl.equations._eqn_10
| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
 ::⟨(el, []), [(μ', .(shape')), (σ', .(shape')), (z', .(shape'))], operator.det (det.op.mvn_iso_empirical_kl shape')⟩
 ::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint :=
begin
assertv H_ok : μ = μ' ∧ σ = σ' ∧ z = z' ∧ shape = shape' ∧ eloss = el ∧ σ ≠ μ := H_pre^.left,

cases H_ok with H_μ H_ok, subst H_μ,
cases H_ok with H_σ H_ok, subst H_σ,
cases H_ok with H_z H_ok, subst H_z,
cases H_ok with H_shape H_ok, subst H_shape,
cases H_ok with H_eloss_eq_el H_σ_neq_μ, subst H_eloss_eq_el,

dunfold graph.to_dist operator.to_dist dvec.head integrate_mvn_iso_kl,
simp [E.E_bind, E.E_ret],
dunfold dvec.head, dsimp,

assertv H_μ_mem : (μ, shape) ∈ env.keys inputs := env.has_key_mem_keys (H_ps_in_env^.left (μ, shape) (mem_cons_self _ _)),
assertv H_σ_mem : (σ, shape) ∈ env.keys inputs := env.has_key_mem_keys (H_ps_in_env^.left (σ, shape) (mem_cons_of_mem _ (mem_cons_self _ _))),
assertv H_z_mem : (z, shape) ∈ (z,shape) :: (eloss, []) :: map node.ref nodes := mem_of_cons_same,
assertv H_eloss_mem : (eloss, []) ∈ (z, shape) :: (eloss, []) :: map node.ref nodes := mem_cons_of_mem _ mem_of_cons_same,

assertv H_μ_neq_z : (μ, shape) ≠ (z, shape) := nodup_append_neq H_μ_mem H_z_mem H_nodup,
assertv H_σ_neq_z : (σ, shape) ≠ (z, shape) := nodup_append_neq H_σ_mem H_z_mem H_nodup,
assertv H_μ_neq_eloss : (μ, shape) ≠ (eloss, []) := nodup_append_neq H_μ_mem H_eloss_mem H_nodup,
assertv H_σ_neq_eloss : (σ, shape) ≠ (eloss, []) := nodup_append_neq H_σ_mem H_eloss_mem H_nodup,
assertv H_eloss_neq_z : (eloss, []) ≠ (z, shape) := ne.symm (nodup_cons_neq mem_of_cons_same (nodup_of_nodup_append_right H_nodup)),

dunfold env.get_ks,
tactic.dget_dinsert,

erw [det.op.f.equations._eqn_5],--, det.special.f.equations._eqn_10],
erw [det.op.f.equations._eqn_4, det.special.f.equations._eqn_10],
dunfold det.function.mvn_iso_kl det.function.mvn_iso_empirical_kl dvec.head dvec.head2 dvec.head3,

-- TODO(dhs): I think this is a bug in LEAN. (z, shape) and (eloss, []) are in the type of the last argument.
simp only [λ (x : dvec T [shape]),
               @env.insert_insert_flip (z, shape) (eloss, [])
                                       x^.head (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs (ne.symm H_eloss_neq_z)],

-- Two steps:
-- 1. Split out eloss, and prove that it equals the lookup val
-- 2. For RHS, use eloss not appearing to remove them both
dunfold sum_costs map sumr,

-- Step 1

definev k₁ : env → ℝ := λ (m : env), env.get (eloss, @nil ℕ) m,
definev k₂ : env → ℝ := λ (m : env), sumr (map (λ (cost : ID), env.get (cost, @nil ℕ) m) costs),

definev m_lhs_k_add : dvec T [shape] → env := λ (x : dvec T [shape]), env.insert (eloss, @nil ℕ) (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape))
                                                                             (env.insert (z, shape) (dvec.head x) inputs),


assert H_lhs_kint₁ : ∀ (x : dvec T [shape]), is_gintegrable (λ m, ⟦k₁ m⟧) (m_lhs_k_add x) nodes dvec.head,
 { dsimp [is_gintegrable, integrate_mvn_iso_kl, dvec.head] at H_kl_gint, dsimp, intro x,
   cases x with xx x xxx xnil, cases xnil,
   simp only [λ a1 a2 a3, @env.insert_insert_flip (eloss, []) (z, shape) a1 a2 a3 H_eloss_neq_z],
   simp only [det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs] at H_kl_gint,
   dunfold sumr map at H_kl_gint,
   exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_kl_gint^.right x))^.left
  },

assert H_lhs_kint₂ : ∀ (x : dvec T [shape]), is_gintegrable (λ m, ⟦k₂ m⟧) (m_lhs_k_add x) nodes dvec.head,
 { dsimp [is_gintegrable, integrate_mvn_iso_kl, dvec.head] at H_kl_gint, dsimp, intro x,
   cases x with xx x xxx xnil, cases xnil,
   simp only [λ a1 a2 a3, @env.insert_insert_flip (eloss, []) (z, shape) a1 a2 a3 H_eloss_neq_z],
   simp only [det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs] at H_kl_gint,
   dunfold sumr map at H_kl_gint,
   exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_kl_gint^.right x))^.right },

simp only [(λ (x : dvec T [shape]), E.E_k_add k₁ k₂ (m_lhs_k_add x) nodes (H_lhs_kint₁ x) (H_lhs_kint₂ x))],

clear H_lhs_kint₁ H_lhs_kint₂,

definev m_rhs_k_add : dvec T [shape] → env := λ x, env.insert (eloss, @nil ℕ)
                                                              (T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (dvec.head x))
                                                              (env.insert (z, shape) (dvec.head x) inputs),

assert H_rhs_kint₁ : ∀ (x : dvec T [shape]), is_gintegrable (λ m, ⟦k₁ m⟧) (m_rhs_k_add x) nodes dvec.head,
 { dsimp [is_gintegrable, integrate_mvn_iso_kl, dvec.head] at H_gint, dsimp, intro x,
   cases x with xx x xxx xnil, cases xnil,
   simp only [det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs, det.function.mvn_iso_empirical_kl] at H_gint,
   tactic.dget_dinsert_at `H_gint,
   dunfold sumr map dvec.head dvec.head2 dvec.head3 at H_gint,
   exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.left },

assert H_rhs_kint₂ : ∀ (x : dvec T [shape]), is_gintegrable (λ m, ⟦k₂ m⟧) (m_rhs_k_add x) nodes dvec.head,
 { dsimp [is_gintegrable, integrate_mvn_iso_kl, dvec.head] at H_gint, dsimp, intro x,
   cases x with xx x xxx xnil, cases xnil,
   simp only [det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs, det.function.mvn_iso_empirical_kl] at H_gint,
   tactic.dget_dinsert_at `H_gint,
   dunfold sumr map dvec.head dvec.head2 dvec.head3 at H_gint,
   exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.right },

simp only [(λ (x : dvec T [shape]), E.E_k_add k₁ k₂ (m_rhs_k_add x) nodes (H_rhs_kint₁ x) (H_rhs_kint₂ x))],

clear H_rhs_kint₁ H_rhs_kint₂,

pose d_base := sprog.prim (rand.op.mvn_iso shape) ⟦env.get (μ, shape) inputs, env.get (σ, shape) inputs⟧,
pose lhs_f₁ := λ x, E (graph.to_dist (λ (m : env), ⟦k₁ m⟧) (m_lhs_k_add x) nodes) dvec.head,
pose lhs_f₂ := λ x, E (graph.to_dist (λ (m : env), ⟦k₂ m⟧) (m_lhs_k_add x) nodes) dvec.head,

assert H_E_kl_add :
∀ x, E (graph.to_dist (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))),
                         ⟦env.get (eloss, @nil ℕ) m + sumr (map (λ (cost : ID), (env.get (cost, @nil ℕ) m : ℝ)) costs)⟧)
            (env.insert (z, shape) x
                        (env.insert (eloss, @nil ℕ) (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs))
            nodes)
       dvec.head
=
E (graph.to_dist (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦k₁ m⟧)
            (env.insert (z, shape) x
                        (env.insert (eloss, @nil ℕ) (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs))
            nodes)
       dvec.head
+
E (graph.to_dist (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦k₂ m⟧)
            (env.insert (z, shape) x
                        (env.insert (eloss, @nil ℕ) (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs))
            nodes)
       dvec.head,
{ intro x,
  exact E.E_k_add k₁ k₂ _ _ (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_kl_gint^.right x))^.left (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_kl_gint^.right x))^.right },

assert H_lhs_eint₁ : E.is_eintegrable d_base lhs_f₁,
{
dsimp [E.is_eintegrable, dvec.head],
dsimp [integrate_mvn_iso_kl, is_gintegrable] at H_kl_gint,
simp only [λ a1 a2 a3, @env.insert_insert_flip (eloss, []) (z, shape) a1 a2 a3 H_eloss_neq_z],
simp only [det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs, det.function.mvn_iso_kl] at H_kl_gint,
tactic.dget_dinsert_at `H_kl_gint,
dunfold sumr map dvec.head dvec.head2 dvec.head3 at H_kl_gint,
simp only [H_E_kl_add] at H_kl_gint,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_kl_gint^.left)^.left
},

assert H_lhs_eint₂ : E.is_eintegrable d_base lhs_f₂,
{
dsimp [E.is_eintegrable, dvec.head],
dsimp [integrate_mvn_iso_kl, is_gintegrable] at H_kl_gint,
simp only [λ a1 a2 a3, @env.insert_insert_flip (eloss, []) (z, shape) a1 a2 a3 H_eloss_neq_z],
simp only [det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs, det.function.mvn_iso_kl] at H_kl_gint,
tactic.dget_dinsert_at `H_kl_gint,
dunfold sumr map dvec.head dvec.head2 dvec.head3 at H_kl_gint,
simp only [H_E_kl_add] at H_kl_gint,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_kl_gint^.left)^.right
},

erw E.E_add d_base lhs_f₁ lhs_f₂ H_lhs_eint₁ H_lhs_eint₂,

pose rhs_f₁ := λ x, E (graph.to_dist (λ (m : env), ⟦k₁ m⟧) (m_rhs_k_add x) nodes) dvec.head,
pose rhs_f₂ := λ x, E (graph.to_dist (λ (m : env), ⟦k₂ m⟧) (m_rhs_k_add x) nodes) dvec.head,

dsimp [graph.to_dist, operator.to_dist, is_gintegrable, integrate_mvn_iso_kl, dvec.head] at H_gint,
simp only [E.E_bind, E.E_ret, det.op.f, det.special.f, dvec.head, env.get_ks, sum_costs, det.function.mvn_iso_empirical_kl] at H_gint,
tactic.dget_dinsert_at `H_gint,

assert H_E_add : ∀ x,
E
         (graph.to_dist
            (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦(env.get (eloss, @nil ℕ) m : ℝ) + sumr (map (λ (cost : ID), (env.get (cost, @nil ℕ) m : ℝ)) costs)⟧)
            (env.insert (eloss, @nil ℕ)
               (T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) x)
               (env.insert (z, shape) x inputs))
            nodes)
         dvec.head
=
E
         (graph.to_dist
            (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦k₁ m⟧)
            (env.insert (eloss, @nil ℕ)
               (T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) x)
               (env.insert (z, shape) x inputs))
            nodes)
         dvec.head
+
E
         (graph.to_dist
            (λ (m : dmap (ID × list ℕ) (λ (ref : ID × list ℕ), T (ref.snd))), ⟦k₂ m⟧)
            (env.insert (eloss, @nil ℕ)
               (T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) x)
               (env.insert (z, shape) x inputs))
            nodes)
         dvec.head,
{
intro x,
exact E.E_k_add k₁ k₂ _ _ (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.left (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_gint^.right x))^.right
},

assert H_rhs_eint₁ : E.is_eintegrable d_base rhs_f₁,
{
dsimp [E.is_eintegrable, dvec.head],
dunfold sumr map dvec.head dvec.head2 dvec.head3 at H_gint,
simp only [H_E_add] at H_gint,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_gint^.left)^.left
},

assert H_rhs_eint₂ : E.is_eintegrable d_base rhs_f₂,
{
dsimp [E.is_eintegrable, dvec.head],
dunfold sumr map dvec.head dvec.head2 dvec.head3 at H_gint,
simp only [H_E_add] at H_gint,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_gint^.left)^.right
},

erw E.E_add d_base rhs_f₁ rhs_f₂ H_rhs_eint₁ H_rhs_eint₂,

clear integrate_mvn_iso_kl_correct,

assert H_eloss_not_in_nodes : (eloss, []) ∉ map node.ref nodes,
{
intro H_eloss_in_nodes,
assertv H_nodup₂ : ∀ (val : T shape), nodup (env.keys (env.insert (z, shape) val inputs) ++ (eloss, []) :: map node.ref nodes) := assume val, env.nodup_insert H_nodup,
assertv H_nodup₃ : nodup ((eloss, []) :: map node.ref nodes) := nodup_of_nodup_append_right (H_nodup₂ 1),
exact not_mem_of_nodup_cons H_nodup₃ H_eloss_in_nodes
},

assert H_eloss_notin : ∀ {x : dvec T [shape]}, (eloss, []) ∉ env.keys (env.insert (z, shape) x^.head inputs) ++ map node.ref nodes,
{
intros x H_eloss_in,
assertv H_nodup₂ : ∀ (val : T shape), nodup (env.keys (env.insert (z, shape) val inputs) ++ (eloss, []) :: map node.ref nodes) := assume val, env.nodup_insert H_nodup,
assertv H_eloss_in_either : (eloss, []) ∈ env.keys (env.insert (z, shape) x^.head inputs) ∨ (eloss, []) ∈ map node.ref nodes := mem_or_mem_of_mem_append H_eloss_in,
cases H_eloss_in_either with H_eloss_in_keys H_eloss_in_nodes,
  { exact nodup_append_neq H_eloss_in_keys mem_of_cons_same (H_nodup₂ x^.head) rfl },
  { exact H_eloss_not_in_nodes H_eloss_in_nodes }
},

assert H_term₁_lhs :
∀ (x : dvec T [shape]),
E (graph.to_dist (λ (m : env), ⟦(λ (m : env), env.get (eloss, []) m) m⟧)
                 (env.insert (eloss, []) (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape))
                              (env.insert (z, shape) (dvec.head x) inputs))
                 nodes)
   dvec.head
=
T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape),
{ intro x, apply (E.E_of_lookup H_eloss_not_in_nodes),
dsimp [pdfs_exist_at] at H_pdfs_exist_at,
dsimp [all_parents_in_env] at H_ps_in_env,
exact (pdfs_exist_at_ignore (H_pre^.right^.right _) H_eloss_notin (H_pdfs_exist_at^.right _))
},

assert H_term₁_rhs :
∀ (x : dvec T [shape]),
E (graph.to_dist (λ (m : env), ⟦(λ (m : env), env.get (eloss, @nil ℕ) m) m⟧)
                 (env.insert (eloss, @nil ℕ)
                   (T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (dvec.head x))
               (env.insert (z, shape) (dvec.head x) inputs))
            nodes)
         dvec.head
=
T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (dvec.head x),
{ intro x, apply (E.E_of_lookup H_eloss_not_in_nodes),
dsimp [pdfs_exist_at] at H_pdfs_exist_at,
dsimp [all_parents_in_env] at H_ps_in_env,
exact (pdfs_exist_at_ignore (H_pre^.right^.right _) H_eloss_notin (H_pdfs_exist_at^.right _))
 },

assert H_term₁ :
E (sprog.prim (rand.op.mvn_iso shape) ⟦env.get (μ, shape) inputs, env.get (σ, shape) inputs⟧)
    (λ (x : dvec T [shape]),
       E
         (graph.to_dist (λ (m : env), ⟦(λ (m : env), env.get (eloss, @nil ℕ) m) m⟧)
            (env.insert (eloss, @nil ℕ) (T.mvn_iso_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape))
               (env.insert (z, shape) (dvec.head x) inputs))
            nodes)
         dvec.head)
=
E (sprog.prim (rand.op.mvn_iso shape) ⟦env.get (μ, shape) inputs, env.get (σ, shape) inputs⟧)
    (λ (x : dvec T [shape]),
         E (graph.to_dist (λ (m : env), ⟦(λ (m : env), env.get (eloss, @nil ℕ) m) m⟧)
                          (env.insert (eloss, @nil ℕ)
                                       (T.mvn_iso_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (dvec.head x))
                                       (env.insert (z, shape) (dvec.head x) inputs))
            nodes)
         dvec.head),
{
simp [H_term₁_lhs, H_term₁_rhs],
dunfold E T.dintegral dvec.head rand.op.pdf dvec.head2 dvec.head3,
dsimp,
dunfold dvec.head,
erw T.integral_fscale,
erw (@T.mvn_iso_kl_identity shape (env.get (μ, shape) inputs) (env.get (σ, shape) inputs) H_pre^.right^.left),
assertv H_pdf_1 : ∫ (λ (x : T shape), T.mvn_iso_pdf (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) x) = 1 := T.mvn_iso_pdf_int1 _ _ H_pre^.right^.left,
delta rand.pdf.mvn_iso,
dsimp,
rw H_pdf_1,
rw T.one_smul
},

erw H_term₁, clear H_term₁, apply congr_arg,
apply congr_arg, apply funext, intro x,
assertv H_ps_in_env : all_parents_in_env (env.insert (z, shape) x^.head inputs) nodes := by apply H_pre^.right^.right,
dsimp,
erw (to_dist_congr_insert H_ps_in_env H_eloss_notin H_eloss_not_cost),
erw (to_dist_congr_insert H_ps_in_env H_eloss_notin H_eloss_not_cost)
end

-- EQ11
--#check integrate_mvn_iso_kl.equations._eqn_11
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], operator.rand op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ12
--#check integrate_mvn_iso_kl.equations._eqn_12
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, []), ((pname₃, shape₃)::(pname₄, shape₄)::(pname₅, shape₅)::parent::parents), op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ13
--#check integrate_mvn_iso_kl.equations._eqn_13
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], operator.rand (rand.op.mvn_iso shape)⟩
  ::⟨(rname₂, (shape₂ :: shapes₂)), parents, op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- EQ14 (a)
--#check integrate_mvn_iso_kl.equations._eqn_14
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), operator.det op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint :=
begin
dunfold graph.to_dist operator.to_dist integrate_mvn_iso_kl,
dunfold integrate_mvn_iso_kl_pre at H_pre,
rw [E.E_bind, E.E_bind],
simp [E.E_ret],

definev next_inputs : env := env.insert (rname₂, shape₂) (op^.f (env.get_ks ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents) inputs)) inputs,
definev next_nodes : list node := nodes,

assertv H_pre_next : integrate_mvn_iso_kl_pre eloss next_nodes next_inputs := H_pre,
assertv H_nodup_next : nodup (env.keys next_inputs ++ map node.ref next_nodes) := env.nodup_insert H_nodup,
assertv H_ps_in_env_next : all_parents_in_env next_inputs next_nodes := H_ps_in_env^.right _,
exact (integrate_mvn_iso_kl_correct _ _ H_eloss_not_cost H_pre_next H_nodup_next H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
end

-- EQ14 (b)
--#check integrate_mvn_iso_kl.equations._eqn_14
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), operator.rand op⟩::nodes) inputs H_eloss_not_cost H_pre H_nodup H_ps_in_env H_pdfs_exist_at H_kl_gint H_gint := false.rec _ H_pre

-- More useful API

def integrate_kl_pre : graph → env → Prop
| g m := integrate_mvn_iso_kl_pre g^.costs^.head g^.nodes m

def integrate_kl : graph → graph
| g := ⟨integrate_mvn_iso_kl g^.costs^.head g^.nodes, g^.costs, g^.targets, g^.inputs⟩

end certigrad
