/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof that we only need to prove that all preconditions are satisfied
to establish both grads_exist_at and pdfs_exist_at.
-/
import .predicates

namespace certigrad

def all_pre_satisfied : list node → env → Prop
| [] _ := true

| (⟨ref, parents, operator.det op⟩ :: nodes) m :=
  op^.pre (env.get_ks parents m) ∧ all_pre_satisfied nodes (env.insert ref (op^.f (env.get_ks parents m)) m)

| (⟨ref, parents, operator.rand op⟩ :: nodes) m :=
  op^.pre (env.get_ks parents m) ∧ (∀ y, all_pre_satisfied nodes (env.insert ref y m))

lemma grads_exist_at_of_all_pre : Π (nodes : list node) (m : env) (tgt : reference), all_pre_satisfied nodes m → grads_exist_at nodes m tgt
| [] _ _ _ := trivial

| (⟨ref, parents, operator.det op⟩ :: nodes) m tgt H_pres :=
begin
dsimp [all_pre_satisfied] at H_pres,
dsimp [grads_exist_at],
split,
exact grads_exist_at_of_all_pre _ _ _ H_pres^.right,
intro H_tgt_in_parents,
split,
exact H_pres^.left,
exact grads_exist_at_of_all_pre _ _ _ H_pres^.right
end

| (⟨ref, parents, operator.rand op⟩ :: nodes) m tgt H_pres :=
begin
dsimp [all_pre_satisfied] at H_pres,
dsimp [grads_exist_at],
split,
intro H_tgt_in_parents,
exact H_pres^.left,
intro y,
exact grads_exist_at_of_all_pre _ _ _ (H_pres^.right y)
end


/-
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
-/
end certigrad
