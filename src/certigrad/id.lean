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

section tactics
open tactic

meta def prove_ids_neq : tactic unit :=
do H ← intro `H,
   Hs ← injection H,
   match Hs with
   | [] := done
   | [H'] := contra_nats_eq H' <|>
             (do H''_ty ← mk_app `certigrad.label.label_eq_of_to_nat [H'],
                 note `H'' none H''_ty,
                 get_local `H'' >>= contra_nats_eq)
   | (x::y::xs) := fail "injection produced multiple hyps"
   end


end tactics

end certigrad
