/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Environments.
-/
import .tensor .id library_dev_extras.util library_dev_extras.dmap .reference

namespace certigrad

-- We wrap `dmap` as `env` to avoid the need for higher-order unification.
@[reducible] def env : Type := dmap reference (λ (ref : reference), T ref.2)

namespace env

def mk : env := dmap.mk
def get (ref : reference) (m : env) : T ref.2 := @dmap.get reference (λ ref, T ref.2) _ _ ref m
def insert (ref : reference) (x : T ref.2) (m : env) : env := @dmap.insert reference (λ ref, T ref.2) _ ref x m
def keys (m : env) : list reference := @dmap.keys reference (λ ref, T ref.2) _ _ m
def has_key (ref : reference) (m : env) : Prop := dmap.has_key ref m

instance decidable_has_key (ref : reference) (m : env) : decidable (has_key ref m) :=
show decidable (dmap.has_key ref m), by tactic.apply_instance

def get_ks : Π (refs : list reference) (m : env), dvec T refs^.p2
| []          m := ⟦⟧
| (ref::refs) m := dvec.cons (get ref m) (get_ks refs m)

def insert_all : Π (refs : list reference) (vs : dvec T refs^.p2), env
| []      ⟦⟧       := env.mk
| (k::ks) (v:::vs) := env.insert k v (insert_all ks vs)

lemma has_key_mem_keys {ref : reference} {m : env} :
  has_key ref m → ref ∈ keys m := dmap.has_key_mem_keys

lemma has_key_insert {ref₁ ref₂ : reference} {x₂ : T ref₂.2} {m : env} :
  has_key ref₁ m → has_key ref₁ (insert ref₂ x₂ m) := dmap.has_key_insert

lemma has_key_insert_same (ref : reference) {x : T ref.2} (m : env) :
  has_key ref (insert ref x m) := dmap.has_key_insert_same ref m

lemma get_insert_same (ref : reference) (x : T ref.2) (m : env) :
  get ref (insert ref x m) = x := dmap.get_insert_same ref x m

lemma get_insert_diff {ref₁ ref₂ : reference} (x₂ : T ref₂.2) (m : env) :
  ref₁ ≠ ref₂ → get ref₁ (insert ref₂ x₂ m) = get ref₁ m := dmap.get_insert_diff x₂ m

lemma insert_get_same (ref : reference) (m : env) :
  insert ref (get ref m) m = m := dmap.insert_get_same ref m

lemma insert_insert_flip {ref₁ ref₂ : reference} (x₁ : T ref₁.2) (x₂ : T ref₂.2) (m : env) :
  ref₁ ≠ ref₂ → insert ref₁ x₁ (insert ref₂ x₂ m) = insert ref₂ x₂ (insert ref₁ x₁ m) := dmap.insert_insert_flip x₁ x₂ m

lemma insert_insert_same (ref : reference) (x₁ x₂ : T ref.2) (m : env) :
  insert ref x₁ (insert ref x₂ m) = insert ref x₁ m := dmap.insert_insert_same ref x₁ x₂ m

lemma nodup_insert {ref : reference} {x : T ref.2} {refs : list reference} {m : env} :
  list.nodup (keys m ++ (ref :: refs)) → list.nodup (keys (insert ref x m) ++ refs) := dmap.nodup_insert

lemma not_mem_of_insert {ref₀ ref : reference} {x : T ref.2} {refs : list reference} {m : env} :
  ref₀ ∉ (keys m ++ (ref :: refs)) → ref₀ ∉ (dmap.keys (dmap.insert ref x m) ++ refs) := dmap.not_mem_of_insert

lemma not_mem_of_insert_symm {ref₀ ref : reference} {x : T ref.2} {refs : list reference} {m : env} :
  ref₀ ∉ (dmap.keys (dmap.insert ref x m) ++ refs) → ref₀ ∉ (keys m ++ (ref :: refs)) := dmap.not_mem_of_insert_symm

section proofs
open list

lemma get_ks_env_eq (m₁ m₂ : env) :
  ∀ (refs : list reference), (∀ (ref : reference), ref ∈ refs → get ref m₁ = get ref m₂) → get_ks refs m₁ = get_ks refs m₂
| [] H := rfl
| (ref::refs) H :=
show get ref m₁ ::: get_ks refs m₁ = get ref m₂ ::: get_ks refs m₂, from
have H_get : get ref m₁ = get ref m₂, from H ref mem_of_cons_same,
have H_pre : ∀ (ref : reference), ref ∈ refs → get ref m₁ = get ref m₂, from
  assume r H_r_mem,
  H r (mem_cons_of_mem _ H_r_mem),
by rw [H_get, get_ks_env_eq _ H_pre]

lemma get_ks_insert_diff :
  ∀ {refs : list reference} {ref : reference} {x : T ref.2} {m : env}, ref ∉ refs → get_ks refs (insert ref x m) = get_ks refs m
| [] _ _ _ _ := rfl
| (ref::refs) ref₀ x m H_ref₀_notin :=
show get ref (insert ref₀ x m) ::: get_ks refs (insert ref₀ x m) = get ref m ::: get_ks refs m, from
have H_ne : ref ≠ ref₀, from ne.symm (ne_of_not_mem_cons H_ref₀_notin),
begin
rw (env.get_insert_diff _ _ H_ne),
rw get_ks_insert_diff (not_mem_of_not_mem_cons H_ref₀_notin),
end

lemma dvec_update_at_env {refs : list reference} {idx : ℕ} {ref : reference} (m : env) :
      at_idx refs idx ref →
      dvec.update_at (get ref m) (get_ks refs m) idx = get_ks refs m :=
begin
intro H_at_idx,
assert H_elem_at_idx : elem_at_idx refs idx ref, { exact elem_at_idx_of_at_idx H_at_idx },
induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH,
{ dsimp [get_ks], erw dvec.update_at.equations._eqn_2, simp [dif_ctx_simp_congr, dif_pos] },
{ dsimp [get_ks], erw dvec.update_at.equations._eqn_3, erw IH (at_idx_of_cons H_at_idx) }
end

lemma dvec_get_get_ks {refs : list reference} {idx : ℕ} {ref : reference} (m : env) :
      at_idx refs idx ref →
      dvec.get ref.2 (get_ks refs m) idx = get ref m :=
begin
intro H_at_idx,
assert H_elem_at_idx : elem_at_idx refs idx ref, { exact elem_at_idx_of_at_idx H_at_idx },
induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH,
{ dunfold get_ks, erw dvec.get.equations._eqn_2, simp [dif_ctx_simp_congr, dif_pos] },
{ dunfold get_ks, erw dvec.get.equations._eqn_3, exact IH (at_idx_of_cons H_at_idx) }
end

end proofs

section simp_lemmas

lemma simp_has_key_insert_same (ref : reference) {x : T ref.2} (m : env) :
  has_key ref (insert ref x m) = true := sorry

lemma simp_has_key_insert_diff (ref₁ ref₂ : reference) {x : T ref₂.2} (m : env) :
  ref₁ ≠ ref₂ → has_key ref₁ (insert ref₂ x m) = has_key ref₁ m := sorry

lemma simp_has_key_empty (ref : reference) : has_key ref env.mk = false := sorry

end simp_lemmas

end env
end certigrad
