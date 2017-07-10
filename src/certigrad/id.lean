/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Identifiers.
-/
import .util .label

namespace certigrad

inductive ID : Type
| str : label → ID
| nat : ℕ → ID

namespace ID

instance : decidable_eq ID := by tactic.mk_dec_eq_instance
instance : inhabited ID := ⟨ID.str label.default⟩

private def add : ID → ID → ID
| (ID.nat n₁) (ID.nat n₂) := ID.nat (n₁ + n₂)
| _           _           := default ID

def to_str : ID → string
| (str l) := to_string l
| (nat n) := "#" ++ to_string n

instance : has_to_string ID := ⟨to_str⟩

def less_than : ID → ID → Prop
| (nat n)  (str s) := true
| (str s)  (nat n) := false
| (nat n₁) (nat n₂) := n₁ < n₂
| (str s₁) (str s₂) := s₁ < s₂

instance : has_lt ID := ⟨less_than⟩

instance decidable_less_than : Π (x y : ID), decidable (x < y)
| (nat n)  (str s) := decidable.true
| (str s)  (nat n) := decidable.false
| (nat n₁) (nat n₂) := show decidable (n₁ < n₂), by apply_instance
| (str s₁) (str s₂) := by apply label.decidable_less_than

end ID

lemma id_str_ne_nat (x : label) (n : ℕ) : (ID.str x ≠ ID.nat n) = true :=
begin apply pextt, intro H, injection H end

lemma id_nat_ne_str (x : label) (n : ℕ) : (ID.nat n ≠ ID.str x) = true :=
begin apply pextt, intro H, injection H end

lemma id_str_ne_str (x₁ x₂ : label) : (ID.str x₁ ≠ ID.str x₂) = (x₁ ≠ x₂) :=
begin
apply propext,
split,
intros H_ne H_eq,
subst H_eq,
exact H_ne rfl,
intros H_ne H_eq,
injection H_eq with H,
exact H_ne H
end

lemma id_nat_ne_nat (n₁ n₂ : ℕ) : (ID.nat n₁ ≠ ID.nat n₂) = (n₁ ≠ n₂) :=
begin
apply propext,
split,
intros H_ne H_eq,
subst H_eq,
exact H_ne rfl,
intros H_ne H_eq,
injection H_eq with H,
exact H_ne H
end

end certigrad
