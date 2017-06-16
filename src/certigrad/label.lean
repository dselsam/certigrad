/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Labels.

Note: this file is just because strings are slow and cumbersome in current Lean.
-/
import .tactics
namespace certigrad

inductive label : Type
| default
| batch_start
| W_encode, h_encode, W_encode_μ, W_encode_logσ₂
| W_decode, h_decode, W_decode_p
| μ, σ, σ₂, log_σ₂, z, encoding_loss, decoding_loss, ε, x, p

namespace label

def to_str : label → string
| default := "<default>"
| batch_start := "batch_start"
| W_encode := "W_encode"
| h_encode := "h_encode"
| W_encode_μ := "W_encode_μ"
| W_encode_logσ₂ := "W_encode_logσ₂"
| W_decode := "W_decode"
| h_decode := "h_decode"
| W_decode_p := "W_decode_p"
| μ := "μ"
| σ := "σ"
| σ₂ := "σ₂"
| log_σ₂ := "log_σ₂"
| z := "z"
| encoding_loss := "encoding_loss"
| decoding_loss := "decoding_loss"
| ε := "ε"
| x := "x"
| p := "p"

instance : has_to_string label := ⟨to_str⟩

def to_nat : label → ℕ
| default := 0
| batch_start := 1
| W_encode := 2
| h_encode := 3
| W_encode_μ := 4
| W_encode_logσ₂ := 5
| W_decode := 6
| h_decode := 7
| W_decode_p := 8
| μ := 9
| σ := 10
| σ₂ := 11
| log_σ₂ := 12
| z := 13
| encoding_loss := 14
| decoding_loss := 15
| ε := 16
| x := 17
| p := 18

section proofs
open tactic

meta def prove_neq_case_core : tactic unit :=
do H ← intro `H,
   trace "before: ", trace_state,
   dunfold_at [`certigrad.label.to_nat] H,
   trace "after: ", trace_state,
   H ← get_local `H,
   ty ← infer_type H,
   nty ← return $ expr.app (expr.const `not []) ty,
   trace nty,
   assert `H_not nty,
   dec_triv,
   exfalso,
   get_local `H_not >>= λ H_not, exact (expr.app H_not H)

lemma eq_iff_to_nat_eq : ∀ x y : label, (x = y) ↔ (to_nat x = to_nat y) :=
begin
intros x y,
split,
{
intro H_eq,
rw H_eq,
},
{
cases x, all_goals { cases y, all_goals { (prove_neq_case_core <|> (intro1 >> reflexivity)) } }
}
end
end proofs

def dec_eq (x y : label) : decidable (x = y) :=
if x^.to_nat = y^.to_nat

--instance : decidable_eq label := by tactic.mk_dec_eq_instance



def less_than (x y : label) : Prop := x^.to_nat < y^.to_nat

instance : has_lt label := ⟨less_than⟩

instance decidable_less_than (x y : label) : decidable (x < y) := by apply nat.decidable_lt

end label
end certigrad
