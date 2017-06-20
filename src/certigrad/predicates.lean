/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Predicates.
-/
import library_dev_extras.util .id .reference .graph .compute_grad
open list

namespace certigrad

def is_downstream (cost : ID) : reference → list node → Prop
| _   [] := false

| tgt (⟨ref, parents, _⟩ :: nodes) :=
  if ref.1 = cost
  then true
  else (tgt ∈ parents ∧ is_downstream ref nodes) ∨ is_downstream tgt nodes

instance decidable_is_downstream (cost : ID) : Π (tgt : reference) (nodes : list node), decidable (is_downstream cost tgt nodes)
| _   [] := decidable.false

| tgt (⟨ref, parents, _⟩ :: nodes) :=
  show decidable (if ref.1 = cost then true else (tgt ∈ parents ∧ is_downstream cost ref nodes) ∨ is_downstream cost tgt nodes), from
  have H₁ : decidable (is_downstream cost ref nodes), from begin apply decidable_is_downstream end,
  have H₂ : decidable (is_downstream cost tgt nodes), from begin apply decidable_is_downstream end,
  by tactic.apply_instance

def all_parents_in_env : Π (inputs : env) (nodes : list node), Prop
| _   [] := true

| inputs (⟨ref, parents, _⟩ :: nodes) :=
  (∀ (parent : reference), parent ∈ parents → env.has_key parent inputs)
  ∧ (∀ (x : T ref.2), all_parents_in_env (env.insert ref x inputs) nodes)

def all_costs_scalars (costs : list ID) : Π (nodes : list node), Prop
| [] := true
| (⟨ref, _, _⟩ :: nodes) := (ref.1 ∈ costs → ref.2 = []) ∧ all_costs_scalars nodes

-- We group the decidable properties
structure well_formed_at (costs : list ID) (nodes : list node) (inputs : env) (tgt : reference) : Prop :=
  (uids : uniq_ids nodes inputs)
  (ps_in_env : all_parents_in_env inputs nodes)
  (costs_scalars : all_costs_scalars costs nodes)
  (m_contains_tgt : env.has_key tgt inputs)
  (tgt_cost_scalar : tgt.1 ∈ costs → tgt.2 = [])

def grads_exist_at : list node → env → reference → Prop
| [] _ _ := true

| (⟨ref, parents, operator.det op⟩ :: nodes) m tgt  :=
  let m' := env.insert ref (op^.f (env.get_ks parents m)) m in
  grads_exist_at nodes m' tgt
  ∧ (tgt ∈ parents → op^.pre (env.get_ks parents m) ∧ grads_exist_at nodes (env.insert ref (op^.f (env.get_ks parents m)) m) ref)

| (⟨ref, parents, operator.rand op⟩ :: nodes) m tgt  :=
  let m' := (λ (y : T ref.2), env.insert ref y m) in
  (tgt ∈ parents → op^.pre (env.get_ks parents m)) ∧ (∀ y, grads_exist_at nodes (m' y) tgt)

def pdfs_exist_at : list node → env → Prop
| [] _ := true

| (⟨ref, parents, operator.det op⟩ :: nodes) m := pdfs_exist_at nodes (env.insert ref (op^.f (env.get_ks parents m)) m )

| (⟨ref, parents, operator.rand op⟩ :: nodes) m :=
  let m' := (λ (y : T ref.2), env.insert ref y m) in
  (op^.pre (env.get_ks parents m)) ∧ (∀ y, pdfs_exist_at nodes (m' y))

-- TODO(dhs): these conditions are really nitty-gritty
noncomputable def can_differentiate_under_integrals (costs : list ID) : list node → env → reference → Prop
| [] _ _ := true

| (⟨ref, parents, operator.det op⟩ :: nodes) inputs tgt  :=
  let inputs' := env.insert ref (op^.f (env.get_ks parents inputs)) inputs in
  can_differentiate_under_integrals nodes inputs' tgt
  ∧ (tgt ∈ parents → can_differentiate_under_integrals nodes (env.insert ref (op^.f (env.get_ks parents inputs)) inputs) ref)

| (⟨ref, parents, operator.rand op⟩ :: nodes) inputs tgt  :=
  let θ : T tgt.2 := env.get tgt inputs in
  let g : T ref.2 → T tgt.2 → ℝ :=
  (λ (x : T ref.2) (θ₀ : T tgt.2),
      E (graph.to_dist (λ (inputs : env), ⟦sum_costs inputs costs⟧)
                       (env.insert ref x (env.insert tgt θ₀ inputs))
                       nodes)
        dvec.head) in
  let next_inputs := (λ (y : T ref.2), env.insert ref y inputs) in
-- Note: these conditions are redundant, but it is convenient to collect all the variations we need in one place
 ( (T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ₀ inputs)) x ⬝ g x θ₀) θ
    ∧ T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ inputs)) x ⬝ g x θ₀) θ)

    ∧ (T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), ∇ (λ (θ₁ : T (tgt.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ₁ inputs)) x ⬝ g x θ₁) θ₀) θ
       ∧ T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), ∇ (λ (θ₁ : T (tgt.snd)), rand.op.pdf op (env.get_ks parents (env.insert tgt θ inputs)) x ⬝ g x θ₁) θ₀) θ)

    ∧ (∀ (idx : ℕ), at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)), rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx) x ⬝ g x θ) θ)
   ∧ (∀ (idx : ℕ),  at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)),
                                         ∇ (λ (θ₀ : T (tgt.snd)), rand.op.pdf op (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ inputs)) idx) x ⬝ g x θ) θ₀) θ))
∧ (∀ y, can_differentiate_under_integrals nodes (next_inputs y) tgt)

end certigrad
