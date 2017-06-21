/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Environments.
-/
import data.hash_map library_dev.data.list.sort .tensor .id .util .reference

namespace certigrad

@[reducible] def pre_env : Type := hash_map reference (λ (ref : reference), T ref.2)

namespace pre_env

definition eqv (m₁ m₂ : pre_env) : Prop :=
∀ (ref : reference), m₁^.find ref = m₂^.find ref

local infix ~ := eqv

definition eqv.refl (m : pre_env) : m ~ m :=
assume ref, rfl

definition eqv.symm (m₁ m₂ : pre_env) : m₁ ~ m₂ → m₂ ~ m₁ :=
assume H ref, eq.symm (H ref)

definition eqv.trans (m₁ m₂ m₃ : pre_env) : m₁ ~ m₂ → m₂ ~ m₃ → m₁ ~ m₃ :=
assume H₁ H₂ ref, eq.trans (H₁ ref) (H₂ ref)

instance pdmap.eqv_setoid : setoid pre_env :=
setoid.mk eqv (mk_equivalence eqv eqv.refl eqv.symm eqv.trans)

end pre_env

def env : Type := quot pre_env.eqv

namespace env

def mk : env := quotient.mk (mk_hash_map reference.hash)

def get (ref : reference) (q : env) : T ref.2 := quotient.lift_on q
(λ (m : pre_env),
  match m^.find ref with
  | none := default _
  | some x := x
  end)
begin intros m₁ m₂ H_eqv, simp [H_eqv ref] end

def insert (ref : reference) (x : T ref.2) (q : env) : env := quotient.lift_on q
(λ (m : pre_env), quotient.mk $ m^.insert ref x)
begin
intros m₁ m₂ H_eqv, dsimp, apply quotient.sound,
intros ref',
cases (decidable.em (ref = ref')) with H_eq H_neq,
simp [hash_map.find_insert, dif_ctx_simp_congr, H_eq, dif_pos],
simp [hash_map.find_insert, dif_ctx_simp_congr, H_neq, dif_neg, H_eqv ref'],
end

def has_key (ref : reference) (q : env) : Prop := quotient.lift_on q
(λ (m : pre_env), m^.contains ref)
begin intros m₁ m₂ H_eqv, simp [hash_map.contains, H_eqv ref] end

def get_ks : Π (refs : list reference) (m : env), dvec T refs^.p2
| []          m := ⟦⟧
| (ref::refs) m := dvec.cons (get ref m) (get_ks refs m)

def insert_all : Π (refs : list reference) (vs : dvec T refs^.p2), env
| []      ⟦⟧        := env.mk
| (k::ks) (v:::vs) := env.insert k v (insert_all ks vs)

-- Facts
@[simp] lemma get.def (ref : reference) (m : pre_env) :
get ref (quotient.mk m) = match m^.find ref with | none := default _ | some x := x end := rfl

@[simp] lemma insert.def {ref : reference} {x : T ref.2} (m : pre_env) :
insert ref x (quotient.mk m) = quotient.mk (m^.insert ref x) :=
begin apply quotient.sound, apply pre_env.eqv.refl end

@[simp] lemma has_key.def (ref : reference) (m : pre_env) :
has_key ref (quotient.mk m) = m^.contains ref := rfl

@[simp] lemma bool_lift_t (b : bool) : (lift_t b : Prop) = (b = tt) := rfl

-- TODO(dhs): PR to standard library
lemma not_has_key_empty (ref : reference) : ¬ env.has_key ref env.mk :=
begin
simp [mk],
rw hash_map.contains_iff,
simp [hash_map.keys, hash_map.entries, mk_hash_map, bucket_array.as_list,
      mk_array, array.foldl, array.iterate, array.iterate_aux, list.map, array.read],
end

lemma has_key_insert {ref₁ ref₂ : reference} {x₂ : T ref₂.2} {m : env} :
  has_key ref₁ m → has_key ref₁ (insert ref₂ x₂ m) :=
begin
apply @quotient.induction_on _ _ (λ m, has_key ref₁ m → has_key ref₁ (insert ref₂ x₂ m)),
clear m,
intro m,
intro H_hk,
simp at *,
dsimp [hash_map.contains] at *,
rw hash_map.find_insert,
cases decidable.em (ref₂ = ref₁) with H_eq H_neq,
{
subst H_eq,
simp [dif_ctx_simp_congr, dif_pos],
dunfold option.is_some,
reflexivity,
},
{
simp [H_neq, dif_ctx_simp_congr, dif_neg],
exact H_hk
}
end

lemma has_key_insert_same (ref : reference) {x : T ref.2} (m : env) : has_key ref (insert ref x m) :=
begin
apply quotient.induction_on m,
clear m,
intro m,
simp,
dunfold hash_map.contains,
rw hash_map.find_insert_eq,
dsimp [option.is_some],
reflexivity
end

lemma has_key_insert_diff {ref₁ ref₂ : reference} {x : T ref₂.2} {m : env} :
  ref₁ ≠ ref₂ → has_key ref₁ (insert ref₂ x m) → has_key ref₁ m :=
begin
apply @quotient.induction_on _ _ (λ m, ref₁ ≠ ref₂ → has_key ref₁ (insert ref₂ x m) → has_key ref₁ m),
clear m,
simp [hash_map.contains],
intros m H_neq,
rw hash_map.find_insert_ne,
intro H, exact H,
exact ne.symm H_neq
end

lemma get_insert_same (ref : reference) (x : T ref.2) (m : env) : get ref (insert ref x m) = x :=
begin
apply quotient.induction_on m, clear m, intro m,
simp,
rw hash_map.find_insert_eq,
end

lemma get_insert_diff {ref₁ ref₂ : reference} (x₂ : T ref₂.2) (m : env) : ref₁ ≠ ref₂ → get ref₁ (insert ref₂ x₂ m) = get ref₁ m :=
begin
apply @quotient.induction_on _ _ (λ m, ref₁ ≠ ref₂ → get ref₁ (insert ref₂ x₂ m) = get ref₁ m),
clear m,
intros m H_neq,
simp,
rw hash_map.find_insert,
-- TODO(dhs): annoying that we can't simplify inside the major premise
assert H_dif : (dite (ref₂ = ref₁) (λ h, some (eq.rec_on h x₂ : T ref₁.2)) (λ h, hash_map.find m ref₁)) = hash_map.find m ref₁,
simp [dif_ctx_simp_congr, dif_neg, ne.symm H_neq],
rw H_dif,
end

-- TODO(dhs): propagate precondition
lemma insert_get_same {ref : reference} {m : env} : has_key ref m → insert ref (get ref m) m = m :=
begin
apply @quotient.induction_on _ _ (λ m, has_key ref m → insert ref (get ref m) m = m),
clear m,
simp [hash_map.contains],
intros m H_has_key,
apply quotient.sound,
intro ref',
cases decidable.em (ref' = ref) with H_eq H_neq,
{
subst H_eq,
rw hash_map.find_insert_eq,
cases (hash_map.find m ref'),
{ dsimp [option.is_some] at H_has_key, injection H_has_key },
dsimp,
reflexivity
},
{
rw hash_map.find_insert_ne,
exact ne.symm H_neq
}
end

lemma insert_insert_flip {ref₁ ref₂ : reference} (x₁ : T ref₁.2) (x₂ : T ref₂.2) (m : env) :
  ref₁ ≠ ref₂ → insert ref₁ x₁ (insert ref₂ x₂ m) = insert ref₂ x₂ (insert ref₁ x₁ m) :=
begin
apply @quotient.induction_on _ _ (λ m, ref₁ ≠ ref₂ → insert ref₁ x₁ (insert ref₂ x₂ m) = insert ref₂ x₂ (insert ref₁ x₁ m)),
clear m,
simp,
intros m H_neq,
apply quot.sound,
intro ref,
simp [hash_map.find_insert],
cases decidable.em (ref₁ = ref) with H_eq₁ H_neq₁,
cases decidable.em (ref₂ = ref) with H_eq₂ H_neq₂,
{ exfalso, exact H_neq (eq.trans H_eq₁ (eq.symm H_eq₂)) },
{ subst H_eq₁, simp [H_neq₂, dif_ctx_simp_congr, dif_neg, dif_pos] },
cases decidable.em (ref₂ = ref) with H_eq₂ H_neq₂,
{ subst H_eq₂, simp [H_neq₁, dif_ctx_simp_congr, dif_neg, dif_pos] },
{ simp [H_neq₁, H_neq₂, dif_ctx_simp_congr, dif_neg], }
end

lemma insert_insert_same (ref : reference) (x₁ x₂ : T ref.2) (m : env) :
  insert ref x₁ (insert ref x₂ m) = insert ref x₁ m :=
begin
apply quotient.induction_on m,
clear m,
simp,
intros m,
apply quot.sound,
intro ref',
cases decidable.em (ref' = ref) with H_eq H_neq,
{ subst H_eq, simp [hash_map.find_insert_eq] },
-- TODO(dhs): simp fails for annoying reasons
rw hash_map.find_insert_ne _ _ _ _ (ne.symm H_neq),
rw hash_map.find_insert_ne _ _ _ _ (ne.symm H_neq),
rw hash_map.find_insert_ne _ _ _ _ (ne.symm H_neq)
end

lemma get_ks_env_eq (m₁ m₂ : env) :
  ∀ (refs : list reference), (∀ (ref : reference), ref ∈ refs → get ref m₁ = get ref m₂) → get_ks refs m₁ = get_ks refs m₂
| [] H := rfl
| (ref::refs) H :=
show get ref m₁ ::: get_ks refs m₁ = get ref m₂ ::: get_ks refs m₂, from
have H_get : get ref m₁ = get ref m₂, from H ref list.mem_of_cons_same,
have H_pre : ∀ (ref : reference), ref ∈ refs → get ref m₁ = get ref m₂, from
  assume r H_r_mem,
  H r (list.mem_cons_of_mem _ H_r_mem),
by rw [H_get, get_ks_env_eq _ H_pre]

lemma get_ks_insert_diff :
  ∀ {refs : list reference} {ref : reference} {x : T ref.2} {m : env}, ref ∉ refs → get_ks refs (insert ref x m) = get_ks refs m
| [] _ _ _ _ := rfl
| (ref::refs) ref₀ x m H_ref₀_notin :=
show get ref (insert ref₀ x m) ::: get_ks refs (insert ref₀ x m) = get ref m ::: get_ks refs m, from
have H_ne : ref ≠ ref₀, from ne.symm (list.ne_of_not_mem_cons H_ref₀_notin),
begin
rw (env.get_insert_diff _ _ H_ne),
rw get_ks_insert_diff (list.not_mem_of_not_mem_cons H_ref₀_notin),
end

lemma dvec_update_at_env {refs : list reference} {idx : ℕ} {ref : reference} (m : env) :
      list.at_idx refs idx ref →
      dvec.update_at (get ref m) (get_ks refs m) idx = get_ks refs m :=
begin
intro H_at_idx,
assert H_elem_at_idx : list.elem_at_idx refs idx ref, { exact list.elem_at_idx_of_at_idx H_at_idx },
induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH,
{ dsimp [get_ks], erw dvec.update_at.equations._eqn_2, simp [dif_ctx_simp_congr, dif_pos] },
{ dsimp [get_ks], erw dvec.update_at.equations._eqn_3, erw IH (list.at_idx_of_cons H_at_idx) }
end

lemma dvec_get_get_ks {refs : list reference} {idx : ℕ} {ref : reference} (m : env) :
      list.at_idx refs idx ref →
      dvec.get ref.2 (get_ks refs m) idx = get ref m :=
begin
intro H_at_idx,
assert H_elem_at_idx : list.elem_at_idx refs idx ref, { exact list.elem_at_idx_of_at_idx H_at_idx },
induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH,
{ dunfold get_ks, erw dvec.get.equations._eqn_2, simp [dif_ctx_simp_congr, dif_pos] },
{ dunfold get_ks, erw dvec.get.equations._eqn_3, exact IH (list.at_idx_of_cons H_at_idx) }
end

end env
end certigrad
