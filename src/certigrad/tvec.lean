/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of dvecs of tensors.

We often want to do algebra manipulations on an entire dvec at a time,
and this file makes it possible to use standard notation when doing so.
-/
import .tensor .dvec .util .graph

namespace certigrad

namespace tvec

def lift0 (f : Π {shape : S}, T shape) : Π (shapes : list S), dvec T shapes
| [] := dvec.nil
| (shape::shapes) := dvec.cons f (lift0 shapes)

instance {shapes : list S} : has_zero (dvec T shapes) :=
⟨tvec.lift0 (λ sh, 0) shapes⟩

instance {shapes : list S} : has_one (dvec T shapes) :=
⟨tvec.lift0 (λ sh, 1) shapes⟩

def lift1 (f : Π {shape : S}, T shape → T shape) : Π {shapes : list S}, dvec T shapes → dvec T shapes
| [] _ := dvec.nil
| (shape::shapes) (dvec.cons x xs) := dvec.cons (f x) (lift1 xs)

instance {shapes : list S} : has_neg (dvec T shapes) :=
⟨@tvec.lift1 (λ sh x, - x) shapes⟩

instance {shapes : list S} : has_inv (dvec T shapes) :=
⟨@tvec.lift1 (λ sh x, x⁻¹) shapes⟩

def sqrt {shapes : list S} (xs : dvec T shapes) : dvec T shapes :=
lift1 @T.sqrt xs

def lift2 (f : Π {shape : S}, T shape → T shape → T shape) : Π (shapes : list S), dvec T shapes → dvec T shapes → dvec T shapes
| [] _ _ := dvec.nil
| (shape::shapes) (dvec.cons x xs) (dvec.cons y ys) := dvec.cons (f x y) (lift2 shapes xs ys)

instance {shapes : list S} : has_add (dvec T shapes) :=
⟨tvec.lift2 (λ sh x y, x + y) shapes⟩

instance {shapes : list S} : has_mul (dvec T shapes) :=
⟨tvec.lift2 (λ sh x y, x * y) shapes⟩

instance {shapes : list S} : has_sub (dvec T shapes) :=
⟨tvec.lift2 (λ sh x y, x - y) shapes⟩

instance {shapes : list S} : has_div (dvec T shapes) :=
⟨tvec.lift2 (λ sh x y, x / y) shapes⟩

def scalar_mul : Π (shapes : list S), ℝ → dvec T shapes → dvec T shapes
| [] α _ := dvec.nil
| (shape::shapes) α (dvec.cons x xs) := dvec.cons (α ⬝ x) (scalar_mul shapes α xs)

instance {shapes : list S} : has_smul (ℝ) (dvec T shapes) :=
⟨tvec.scalar_mul shapes⟩

----- Build env from dvec
def to_env_core : Π (names : list ID) (shapes : list S) (xs : dvec T shapes), env
| (name::names) (shape::shapes) (dvec.cons x xs) := env.insert (name, shape) x (to_env_core names shapes xs)
| _ _ _ := env.mk

def to_env (refs : list reference) (xs : dvec T refs^.p2) : env := to_env_core refs^.p1 refs^.p2 xs

-- Build dvec from env
def from_env : Π (tgts : list reference) (m : env), dvec T tgts^.p2
| (tgt::tgts) m := (env.get tgt m) ::: (from_env tgts m)
| [] _ := ⟦⟧

open list
lemma get_from_env {refs : list reference} {idx : ℕ} {ref : reference} (H_at_idx : at_idx refs idx ref) (m : env) :
  dvec.get ref.2 (from_env refs m) idx = env.get ref m :=
begin
assertv H_elem_at_idx : elem_at_idx refs idx ref := elem_at_idx_of_at_idx H_at_idx,
induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH,
{ dunfold from_env, erw dvec.get.equations._eqn_2, simp },
{ dunfold from_env, erw dvec.get.equations._eqn_3, exact IH (at_idx_of_cons H_at_idx) }
end

end tvec
end certigrad
