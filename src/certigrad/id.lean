/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Identifiers.
-/
import library_dev_extras.util .label

namespace certigrad

inductive ID : Type
| str : label → ID
| nat : ℕ → ID

namespace ID

instance coe_label_to_ID : has_coe label ID := ⟨ID.str⟩

instance : decidable_eq ID := by tactic.mk_dec_eq_instance
instance : inhabited ID := ⟨label.default⟩

private def add : ID → ID → ID
| (ID.nat n₁) (ID.nat n₂) := ID.nat (n₁ + n₂)
| _           _           := default ID

/-
private def zero : ID := ID.nat 0
private def one : ID := ID.nat 1

instance : has_add ID := ⟨add⟩
instance : has_zero ID := ⟨zero⟩
instance : has_one ID := ⟨one⟩
-/
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
end certigrad
