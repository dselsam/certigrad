/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Expected values.
-/
import .sprog .graph .tfacts .compute_grad .tcont .predicates .tactics

namespace certigrad
namespace E
open sprog list

lemma E_ret {oshape : S} : Π {shapes : list S} (xs : dvec T shapes) (f : dvec T shapes → T oshape), E (sprog.ret xs) f = f xs
| [] ⟦⟧ f                            := rfl
| [d] ⟦x⟧ f                          := rfl
| (d₁::d₂::ds) (x₁ ::: x₂ ::: xs) f := rfl

lemma E_bind {oshape : S} : Π {shapes₁ shapes₂ : list S} (start : sprog shapes₁) (rest : dvec T shapes₁ → sprog shapes₂) (f : dvec T shapes₂ → T oshape),
  E (sprog.bind start rest) f = (E start) (λ (x : dvec T shapes₁), (E (rest x) f))
| shapes₁ [] start rest f                := rfl
| shapes₁ [s] start rest f               := rfl
| shapes₁ (s₁::s₂::shapes₂) start rest f := rfl

noncomputable def is_eintegrable {oshape : S} : Π {shapes : list S}, sprog shapes → (dvec T shapes → T oshape) → Prop
| shapes (@sprog.ret .(shapes) xs) f := true

| shapes (@sprog.bind shapes₁ .(shapes) start rest) f :=
is_eintegrable start (λ (x : dvec T shapes₁), E (rest x) f) ∧ ∀ (x : dvec T shapes₁), is_eintegrable (rest x) f

| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f := T.is_integrable (λ (x : T oshape), pd^.pdf args x ⬝ f ⟦x⟧)

lemma is_eintegrable_ret {oshape : S} : Π {shapes : list S} (xs : dvec T shapes) (f : dvec T shapes → T oshape), is_eintegrable (sprog.ret xs) f = true
| [] ⟦⟧ f                            := rfl
| [d] ⟦x⟧ f                          := rfl
| (d₁::d₂::ds) (x₁ ::: x₂ ::: xs) f := rfl

lemma is_eintegrable_bind {oshape : S} : Π {shapes₁ shapes₂ : list S} (start : sprog shapes₁) (rest : dvec T shapes₁ → sprog shapes₂) (f : dvec T shapes₂ → T oshape),
  is_eintegrable (sprog.bind start rest) f = (is_eintegrable start (λ (x : dvec T shapes₁), E (rest x) f) ∧ ∀ (x : dvec T shapes₁), is_eintegrable (rest x) f)
| shapes₁ [] start rest f                := rfl
| shapes₁ [s] start rest f               := rfl
| shapes₁ (s₁::s₂::shapes₂) start rest f := rfl

lemma E_add {fshape : S} : Π {shapes : list S} (d : sprog shapes) (f₁ f₂ : dvec T shapes → T fshape),
  is_eintegrable d f₁ → is_eintegrable d f₂ →
  E d (λ x, f₁ x + f₂ x) = E d f₁ + E d f₂
| shapes (@sprog.ret .(shapes) xs) f₁ f₂ Hf₁ Hf₂ := by simp only [E_ret]
| shapes (@sprog.bind shapes₁ .(shapes) start rest) f₁ f₂ Hf₁ Hf₂ :=
have H₁ : ∀ x, is_eintegrable (rest x) f₁, begin simp only [is_eintegrable_bind] at Hf₁, exact Hf₁^.right end,
have H₂ : ∀ x, is_eintegrable (rest x) f₂, begin simp only [is_eintegrable_bind] at Hf₂, exact Hf₂^.right end,

have G₁ : is_eintegrable start (λ (x : dvec T shapes₁), E (rest x) f₁), begin simp only [is_eintegrable_bind] at Hf₁, exact Hf₁^.left end,
have G₂ : is_eintegrable start (λ (x : dvec T shapes₁), E (rest x) f₂), begin simp only [is_eintegrable_bind] at Hf₂, exact Hf₂^.left end,

by simp only [E_bind, (λ x, E_add (rest x) _ _ (H₁ x) (H₂ x)), E_add start _ _ G₁ G₂]

| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f₁ f₂ Hf₁ Hf₂ :=

have H₁ : T.is_dintegrable (λ (xs : dvec T [oshape]), rand.op.pdf pd args (dvec.head xs) ⬝ f₁ xs),
 begin dunfold T.is_dintegrable T.dintegral dvec.head, split, exact Hf₁, intro ignore, exact trivial end,

have H₂ : T.is_dintegrable (λ (xs : dvec T [oshape]), rand.op.pdf pd args (dvec.head xs) ⬝ f₂ xs),
 begin dunfold T.is_dintegrable T.dintegral dvec.head, split, exact Hf₂, intro ignore, exact trivial end,

T.dintegral_add_middle _ _ _ H₁ H₂

-- TODO(dhs): need WF
lemma is_eintegrable_add {oshape : S} : Π {shapes : list S} (d : sprog shapes) (f₁ f₂ : dvec T shapes → T oshape),
  (is_eintegrable d f₁ ∧ is_eintegrable d f₂) ↔ is_eintegrable d (λ x, f₁ x + f₂ x) := sorry
-- TODO(dhs): commented only because we don't have WF
/-
| shapes (@sprog.ret .(shapes) xs) f₁ f₂ :=

begin
simp only [is_eintegrable_ret],
split, intro, exact trivial, intro, split, exact trivial, exact trivial
end

| shapes (@sprog.bind shapes₁ .(shapes) start rest) f₁ f₂ :=
begin
split,
{
simp only [is_eintegrable_bind],
intro H,
cases H with H₁ H₂,
split,
{ simp only [(λ x, E_add (rest x) _ _ (H₁^.right x) (H₂^.right x))],
  apply iff.mp (is_eintegrable_add _ _ _) (and.intro H₁^.left H₂^.left) },
{ intro x, exact iff.mp (is_eintegrable_add _ _ _) (and.intro (H₁^.right x) (H₂^.right x)) }
},
{
intro H,
exact iff.mpr (is_eintegrable_add _ _ _) H
}
end

| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f₁ f₂ :=
is_eintegrable_add (sprog.prim pd args) f₁ f₂
-/

lemma E_congr {shapes : list S} {oshape : S} (d₁ d₂ : sprog shapes) (f : dvec T shapes → T oshape) (H : d₁ = d₂) :
  E d₁ f = E d₂ f := by rw H

lemma E_scale {oshape : S} (α : ℝ) : Π {shapes : list S} (d : sprog shapes) (f : dvec T shapes → T oshape), E d (λ x, α ⬝ f x) = α ⬝ E d f
| shapes (@sprog.ret .(shapes) xs) f := by simp only [E_ret]
| shapes (@sprog.bind shapes₁ .(shapes) start rest) f := by simp only [E_bind, (λ x, E_scale (rest x)), E_scale start]
| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f := begin dunfold E, exact T.dintegral_scale_middle α _ f end

lemma E_scale_mul (α : ℝ) : Π {shapes : list S} (d : sprog shapes) (f : dvec T shapes → ℝ), E d (λ x, α * f x) = α * E d f
| shapes (@sprog.ret .(shapes) xs) f := by simp only [E_ret]
| shapes (@sprog.bind shapes₁ .(shapes) start rest) f := by simp only [E_bind, (λ x, E_scale_mul (rest x)), E_scale_mul start]
| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f := begin dunfold E, exact T.dintegral_mul_middle α _ f end

lemma E_fscale {fshape : S} (y : T fshape) : Π {shapes : list S} (d : sprog shapes) (f : dvec T shapes → ℝ), E d (λ x, f x ⬝ y) = E d f ⬝ y
| shapes (@sprog.ret .(shapes) xs) f := by simp only [E_ret]
| shapes (@sprog.bind shapes₁ .(shapes) start rest) f := by simp only [E_bind, (λ x, E_fscale (rest x)), E_fscale start]
| [oshape] (@sprog.prim ishapes .(oshape) pd args) f :=
begin
dunfold E T.dintegral,
assert H_lam : ∀ x, rand.op.pdf pd args (dvec.head ⟦x⟧) ⬝ (f ⟦x⟧ ⬝ y) = (rand.op.pdf pd args (dvec.head ⟦x⟧) ⬝ f ⟦x⟧) ⬝ y,
{ intro x, erw -T.smul_group, simp only [T.smul.def, T.const_scalar] },
rw [funext H_lam, T.integral_fscale]
end

lemma E_neg {oshape : S} : Π {shapes : list S} (d : sprog shapes) (f : dvec T shapes → T oshape),
  is_eintegrable d f → E d (λ x, - (f x)) = - (E d f)
| shapes (@sprog.ret .(shapes) xs) f Hf := by simp only [E_ret]
| shapes (@sprog.bind shapes₁ .(shapes) start rest) f Hf :=
begin
simp only [is_eintegrable_bind] at Hf,
simp only [E_bind, (λ x, E_neg (rest x) _ (Hf^.right x)), E_neg start _ Hf^.left],
end

| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f Hf := begin dunfold E, exact T.dintegral_neg_middle _ f end

lemma E_const {shapes : list S} {oshape fshape : S} (op : rand.op shapes oshape) (parents : dvec T shapes) (H_op_pre : op^.pre parents) (y : T fshape) :
  E (sprog.prim op parents) (λ x, y) = y :=
T.dintegral_const_middle (λ (x : dvec T [oshape]), op^.pdf parents x^.head)
                         (λ (x : dvec T [oshape]), op^.pdf_pos parents H_op_pre x^.head)
                         (op^.pdf_int1 parents H_op_pre)
                         y

lemma E_bind_assoc : ∀ {shapes₁ shapes₂ shapes₃ : list S} {fshape : S}
                      (d₁ : sprog shapes₁)
                      (d₂ : dvec T shapes₁ → sprog shapes₂)
                      (d₃ : dvec T shapes₂ → sprog shapes₃)
                      (f : dvec T shapes₃ → T fshape),
      E (bind d₁ (λ xs₁, bind (d₂ xs₁) (λ xs₂, d₃ xs₂))) f
      =
      E (bind (bind d₁ (λ xs₁, d₂ xs₁)) (λ xs₂, d₃ xs₂)) f
:=
assume shapes₁ shapes₂ shapes₃ fshape d₁ d₂ d₃ f,
begin
simp only [E_bind],
end

lemma E_pull_out_of_sum {X : Type} {ishapes : list S} {oshape fshape : S}
    (op : rand.op ishapes oshape) (parents : dvec T ishapes) (H_op_pre : op^.pre parents)
    (f : X → dvec T [oshape] → T fshape) :
  ∀ (xs : list X),
  is_eintegrable (sprog.prim op parents) (λ y, sumr (map (λ x, f x y) xs)) →
  sumr (map (λ x, E (sprog.prim op parents) (f x)) xs) = E (sprog.prim op parents) (λ y, sumr (map (λ x, f x y) xs))
| []      H_xs := begin dunfold sumr map, rw E_const, exact H_op_pre end
| (x::xs) H_xs :=
begin
dunfold sumr map,
rw [E_add, E_pull_out_of_sum],
dunfold map sumr at H_xs,
exact (iff.mpr (is_eintegrable_add _ _ _) H_xs)^.right,
exact (iff.mpr (is_eintegrable_add _ _ _) H_xs)^.left,
exact (iff.mpr (is_eintegrable_add _ _ _) H_xs)^.right
end

lemma E_k_add {shape : S} (k₁ k₂ : env → T shape) : Π (m : env) (nodes : list node),
  is_gintegrable (λ m, ⟦k₁ m⟧) m nodes dvec.head →
  is_gintegrable (λ m, ⟦k₂ m⟧) m nodes dvec.head →
  E (graph.to_dist (λ (m : env), ⟦k₁ m + k₂ m⟧) m nodes) dvec.head
  =
  E (graph.to_dist (λ (m : env), ⟦k₁ m⟧) m nodes) dvec.head + E (graph.to_dist (λ (m : env), ⟦k₂ m⟧) m nodes) dvec.head
| m [] Hk₁ Hk₂                                                       :=
begin dunfold graph.to_dist, rw [E_ret, E_ret, E_ret], reflexivity end

| m (⟨ref, parents, operator.det op⟩::nodes) Hk₁ Hk₂ :=
begin
dunfold graph.to_dist operator.to_dist,
simp only [E_ret, E_bind],
rw E_k_add,
exact Hk₁, exact Hk₂
end

| m (⟨ref, parents, operator.rand op⟩::nodes) Hk₁ Hk₂ :=
begin dunfold graph.to_dist operator.to_dist, rw [E_bind, E_bind, E_bind],
dunfold_occs E [1, 2, 3, 5],
dunfold T.dintegral, dsimp,
dsimp [is_gintegrable, dvec.head] at Hk₁ Hk₂,

erw -T.integral_add _ _ Hk₁^.left Hk₂^.left,

apply (congr_arg T.integral), apply funext, intro x,
erw -T.smul_addr,
rw -E_k_add _ _ (Hk₁^.right x) (Hk₂^.right x),
reflexivity
end

lemma E_g_pull_out_of_sum {X : Type} {fshape : S} (f : env → X → T fshape) :
  ∀ (m : env) (nodes : list node) (xs : list X),
  pdfs_exist_at nodes m →
  is_gintegrable (λ m', ⟦sumr (map (λ x, f m' x) xs)⟧) m nodes dvec.head →
  sumr (map (λ x, E (graph.to_dist (λ m', ⟦f m' x⟧) m nodes) dvec.head) xs) = E (graph.to_dist (λ m', ⟦sumr (map (λ x, f m' x) xs)⟧) m nodes) dvec.head
| m [] xs H_pdfs_exist H_gint := by simp only [graph.to_dist, E.E_ret, dvec.head]

| m (⟨ref, parents, operator.det op⟩::nodes) xs H_pdfs_exist H_gint :=
begin
dunfold graph.to_dist operator.to_dist,
simp only [E_ret, E_bind],
apply E_g_pull_out_of_sum,
exact H_pdfs_exist,
exact H_gint
end

| m (⟨ref, parents, operator.rand op⟩::nodes) xs H_pdfs_exist H_gint :=
begin
dunfold graph.to_dist operator.to_dist,
simp only [E.E_ret, E.E_bind],
rw E_pull_out_of_sum _ _ H_pdfs_exist^.left,
apply congr_arg, apply funext, intro y,
rw E_g_pull_out_of_sum _ _ _ (H_pdfs_exist^.right y^.head) (H_gint^.right y^.head),
dsimp [is_eintegrable],
dsimp [is_gintegrable] at H_gint,
simp only [λ (y : dvec T [ref.2]), E_g_pull_out_of_sum _ _ _ (H_pdfs_exist^.right y^.head) (H_gint^.right y^.head)],
exact H_gint^.left
end

end E
open list

-- TODO(dhs): restructure the library
lemma is_gintegrable_k_add {shape : S} (k₁ k₂ : env → T shape) : Π (m : env) (nodes : list node),
  (is_gintegrable (λ m, ⟦k₁ m⟧) m nodes dvec.head ∧ is_gintegrable (λ m, ⟦k₂ m⟧) m nodes dvec.head) ↔ is_gintegrable (λ m, ⟦k₁ m + k₂ m⟧) m nodes dvec.head
| _ [] := begin dsimp [is_gintegrable], split, intro H, exact trivial, intro H, exact (and.intro trivial trivial) end

| m (⟨ref, parents, operator.det op⟩ :: nodes) := begin dsimp [is_gintegrable], apply is_gintegrable_k_add end

| m (⟨ref, parents, operator.rand op⟩ :: nodes) :=
begin
dsimp [is_gintegrable],
split,
{
intro H,
split,
{ simp only [λ x, E.E_k_add k₁ k₂ _ _ (H^.left^.right x) (H^.right^.right x)], apply iff.mp (T.is_integrable_add_middle _ _ _) (and.intro H^.left^.left H^.right^.left) },
intro x,
exact iff.mp (is_gintegrable_k_add _ _) (and.intro (H^.left^.right x) (H^.right^.right x))
},
{
intro H,
assert H_kint₁ : ∀ (x : T (ref.snd)), is_gintegrable (λ (m : env), ⟦k₁ m⟧) (env.insert ref x m) nodes dvec.head,
{ intro x, apply (iff.mpr (is_gintegrable_k_add _ _) (H^.right x))^.left },

assert H_kint₂ : ∀ (x : T (ref.snd)), is_gintegrable (λ (m : env), ⟦k₂ m⟧) (env.insert ref x m) nodes dvec.head,
{ intro x, apply (iff.mpr (is_gintegrable_k_add _ _) (H^.right x))^.right },

split,
{
simp only [λ x, E.E_k_add k₁ k₂ _ _ (H_kint₁ x) (H_kint₂ x)] at H,
split,
{ exact (iff.mpr (T.is_integrable_add_middle _ _ _) H^.left)^.left },
{ intro x, apply (iff.mpr (is_gintegrable_k_add _ _) (H^.right x))^.left }
},
{
simp only [λ x, E.E_k_add k₁ k₂ _ _ (H_kint₁ x) (H_kint₂ x)] at H,
split,
{ exact (iff.mpr (T.is_integrable_add_middle _ _ _) H^.left)^.right },
{ intro x, apply (iff.mpr (is_gintegrable_k_add _ _) (H^.right x))^.right }
},
}
end

namespace E

lemma E_k_tmulT {shape₁ shape₂ : S} (k : env → T shape₂) : Π (m : env) (nodes : list node) (M : T (shape₁ ++ shape₂)),
  E (graph.to_dist (λ (m : env), ⟦T.tmulT M (k m)⟧) m nodes) dvec.head
  =
  T.tmulT M (E (graph.to_dist (λ (m : env), ⟦k m⟧) m nodes) dvec.head)
| m []                                        M :=
begin
dunfold graph.to_dist,
simp [E_ret],
reflexivity
end

| m (⟨ref, parents, operator.det op⟩::nodes)  M :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_ret, E_bind],
rw E_k_tmulT,
end

| m (⟨ref, parents, operator.rand op⟩::nodes) M :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind],
simp [E_k_tmulT],
dunfold E,
rw T.dintegral_tmulT_middle,
end

end E

open list

lemma is_gintegrable_tmulT {ishape oshape : S} (M : T (ishape ++ oshape)) (k : env → T oshape) :
  Π (inputs : env) (nodes : list node),
  is_gintegrable (λ (m : env), ⟦k m⟧) inputs nodes dvec.head ↔ is_gintegrable (λ (m : env), ⟦T.tmulT M (k m)⟧) inputs nodes dvec.head
| inputs [] := iff.intro (λ x, trivial) (λ x, trivial)

| inputs (⟨ref, parents, operator.det op⟩ :: nodes) := by { dsimp [is_gintegrable], apply is_gintegrable_tmulT }

| inputs (⟨ref, parents, operator.rand op⟩ :: nodes) :=
begin
dsimp [is_gintegrable],
split,
{
intro H ,
simp only [E.E_k_tmulT],
split,
  { exact iff.mp (T.is_integrable_tmulT_middle _ _ _) H^.left },
  { intro x, exact iff.mp (is_gintegrable_tmulT _ _) (H^.right x)  }
},
{
intro H,
simp only [E.E_k_tmulT] at H,
split,
  { exact iff.mpr (T.is_integrable_tmulT_middle _ _ _) H^.left },
  { intro x, exact iff.mpr (is_gintegrable_tmulT _ _) (H^.right x) }
}
end

lemma is_gintegrable_of_sumr_map {X : Type} [inhabited X] {shape : S} (k : env → X → T shape) (m : env) (nodes : list node)
  : ∀ (xs : list X) (H_gint : is_gintegrable (λ (m : env), ⟦sumr (map (k m) xs)⟧) m nodes dvec.head) (x : X), x ∈ xs →
      is_gintegrable (λ (m : env), ⟦k m x⟧) m nodes dvec.head
| [] _ x H_in := false.rec _ (not_mem_nil x H_in)

| (x::xs) H_gint y H_in :=
begin
dunfold sumr map at H_gint,
cases (eq_or_mem_of_mem_cons H_in) with H_eq H_in_rec,
{ subst H_eq, exact (iff.mpr (is_gintegrable_k_add _ _ _ _) H_gint)^.left },
{ apply is_gintegrable_of_sumr_map xs (iff.mpr (is_gintegrable_k_add _ _ _ _) H_gint)^.right y H_in_rec }
end

namespace E
open sprog list

lemma E_k_scale {shape : S} (k : env → ℝ) (y : T shape) : Π (m : env) (nodes : list node),
  E (graph.to_dist (λ (m : env), ⟦k m ⬝ y⟧) m nodes) dvec.head
  =
  E (graph.to_dist (λ (m : env), ⟦k m⟧) m nodes) dvec.head ⬝ y
| m []                                        := begin dunfold graph.to_dist, simp [E_ret], refl end
| m (⟨ref, parents, operator.det op⟩::nodes)  :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind, E_ret],
rw E_k_scale
end

| m (⟨ref, parents, operator.rand op⟩::nodes) :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind, E_k_scale, E_fscale],
end

lemma E_k_sum_map {X : Type} [inhabited X] {shape : S} (k : env → X → T shape) : Π (m : env) (nodes : list node) (xs : list X),
  pdfs_exist_at nodes m →
  is_gintegrable (λ m, ⟦sumr (map (k m) xs)⟧) m nodes dvec.head →
  E (graph.to_dist (λ (m : env), ⟦sumr (map (k m) xs)⟧) m nodes) dvec.head
  =
  sumr (map (λ (x : X), E (graph.to_dist (λ (m : env), ⟦k m x⟧) m nodes) dvec.head) xs)
| m [] xs H_pdfs H_ints :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_ret, dvec.head],
end

| m (⟨ref, parents, operator.det op⟩::nodes) xs H_pdfs H_ints :=
begin
dunfold graph.to_dist operator.to_dist,
dsimp [pdfs_exist_at] at H_pdfs,
simp [E_ret, E_bind, dvec.head],
rw E_k_sum_map _ _ _ H_pdfs H_ints
end

| m (⟨ref, parents, operator.rand op⟩::nodes) xs H_pdfs H_ints :=
begin
dunfold graph.to_dist operator.to_dist,
simp only [E_bind],
dunfold pdfs_exist_at at H_pdfs,
dsimp [is_gintegrable] at H_ints,
simp only [λ x, E_k_sum_map _ _ xs (H_pdfs^.right x) (H_ints^.right x)],

rw E_pull_out_of_sum op _ H_pdfs^.left,
dunfold is_eintegrable,

-- TODO(dhs): bad form to do induction in the middle of a proof
-- could make this a lemma
induction xs with x xs IHxs,
{ dunfold sumr map, simp only [T.smul_zero], exact T.is_integrable_zero },
{
dunfold sumr map,
apply iff.mp (T.is_integrable_add_middle (rand.op.pdf op (env.get_ks parents m))
                                      (λ x_1, E (graph.to_dist (λ (m : env), ⟦k m x⟧) (env.insert ref (dvec.head ⟦x_1⟧) m) nodes) dvec.head)
                                      (λ x_1, sumr (map (λ (x : X), E (graph.to_dist (λ (m : env), ⟦k m x⟧) (env.insert ref (dvec.head ⟦x_1⟧) m) nodes) dvec.head) xs))),
dunfold sumr map at H_ints,
simp only [λ x_1, E_k_add (λ m, k m x) (λ m, sumr (map (k m) xs)) (env.insert ref x_1 m) nodes
                      (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_ints^.right x_1))^.left
                      (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_ints^.right x_1))^.right] at H_ints,

split,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_ints^.left)^.left,
apply IHxs,
split,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_ints^.left)^.right,
intro y,
exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_ints^.right y))^.right,
}
end

lemma E_continuous {ishapes : list S} {oshape tshape fshape : S} (pd : rand.op ishapes oshape) (args : T tshape → dvec T ishapes)
                   (f : dvec T [oshape] → T tshape → T fshape) (θ : T tshape) :
  (∀ x, T.is_continuous (λ θ₀, pd^.pdf (args θ₀) x) θ) →
  (∀ x, T.is_continuous (f x) θ) →
  T.is_continuous (λ θ₀, E (sprog.prim pd (args θ₀)) (λ x₀, f x₀ θ₀)) θ :=
assume (H_pdf_continuous : ∀ x, T.is_continuous (λ θ₀, pd^.pdf (args θ₀) x) θ)
       (H_f_continuous : ∀ x, T.is_continuous (f x) θ),
begin
dunfold E T.dintegral,
apply T.integral_continuous,
intro x,
apply T.continuous_scale_fs,
apply H_pdf_continuous,
apply H_f_continuous
end

lemma E_move_fn_to_continuation (shapes : list S) (fshape : S)
                              (k : env → dvec T shapes) (f : dvec T shapes → T fshape) :
  Π (inputs : env) (nodes : list node), E (graph.to_dist k inputs nodes) f = E (graph.to_dist (λ m, ⟦f (k m)⟧) inputs nodes) dvec.head

| m [] :=
begin dunfold graph.to_dist, simp [E_ret], reflexivity end

| m (⟨ref, parents, op⟩::nodes) :=
begin dunfold graph.to_dist, simp [E_bind], apply congr_arg, apply funext, intro x, rw E_move_fn_to_continuation end

lemma E_of_lookup : ∀ {nodes : list node} {inputs : env} {loss : reference} {val : T loss.2},
  loss ∉ map node.ref nodes →
  pdfs_exist_at nodes (env.insert loss val inputs) →
  E (graph.to_dist (λ (m : env), ⟦env.get loss m⟧) (env.insert loss val inputs) nodes) dvec.head = val

| [] inputs loss val H_loss_unused H_pdfs_exist_at :=
begin
dunfold graph.to_dist,
simp [E_ret],
dunfold dvec.head,
rw env.get_insert_same
end

| (⟨ref, parents, operator.det op⟩::nodes) inputs loss val H_loss_unused H_pdfs_exist_at :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind, E_ret],
assertv H_loss_neq_ref : loss ≠ ref := ne_of_not_mem_cons H_loss_unused,
assertv H_loss_unused_next : loss ∉ map node.ref nodes := not_mem_of_not_mem_cons H_loss_unused,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref),
dunfold pdfs_exist_at at H_pdfs_exist_at,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref) at H_pdfs_exist_at,
exact (E_of_lookup H_loss_unused_next H_pdfs_exist_at),
end

| (⟨ref, parents, operator.rand op⟩::nodes) inputs loss val H_loss_unused H_pdfs_exist_at :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind],
assertv H_loss_neq_ref : loss ≠ ref := ne_of_not_mem_cons H_loss_unused,
assertv H_loss_unused_next : loss ∉ map node.ref nodes := not_mem_of_not_mem_cons H_loss_unused,
assert H_inside :
E (sprog.prim op (env.get_ks parents (env.insert loss val inputs)))
    (λ (x_1 : dvec T [ref^.snd]),
       E
         (graph.to_dist (λ (m : env), ⟦env.get loss m⟧)
            (env.insert ref (dvec.head x_1) (env.insert loss val inputs))
            nodes)
         dvec.head)
=
E (sprog.prim op (env.get_ks parents (env.insert loss val inputs)))
    (λ (x_1 : dvec T [ref^.snd]), val),
{
apply congr_arg, apply funext, intro x,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref),
dunfold pdfs_exist_at at H_pdfs_exist_at,
note H_pdfs_exist_at_next := H_pdfs_exist_at^.right x^.head,
dsimp [pdfs_exist_at] at H_pdfs_exist_at_next,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref) at H_pdfs_exist_at_next,
exact (E_of_lookup H_loss_unused_next H_pdfs_exist_at_next)
},

rw H_inside, clear H_inside,
dunfold E T.dintegral dvec.head, dsimp,
rw T.integral_fscale,

assert H_pdf_1 : ∫ (λ (x : T (ref^.snd)), rand.op.pdf op (env.get_ks parents (env.insert loss val inputs)) (dvec.head ⟦x⟧)) = 1,
  { exact op^.pdf_int1 _ H_pdfs_exist_at^.left },

dunfold dvec.head at H_pdf_1,
rw H_pdf_1, rw T.one_smul
end

end E

end certigrad
