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
| W_encode, W_encode₁, W_encode₂, h_encode, W_encode_μ, W_encode_logσ₂
| W_decode, W_decode₁, W_decode₂, h_decode, W_decode_p
| μ, σ, σ₂, log_σ₂, z, encoding_loss, decoding_loss, ε, x, p

namespace label

instance : decidable_eq label := by tactic.mk_dec_eq_instance

def to_str : label → string
| default := "<default>"
| batch_start := "batch_start"
| W_encode := "W_encode"
| W_encode₁ := "W_encode_1"
| W_encode₂ := "W_encode_2"
| h_encode := "h_encode"
| W_encode_μ := "W_encode_mu"
| W_encode_logσ₂ := "W_encode_logs₂"
| W_decode := "W_decode"
| W_decode₁ := "W_decode_1"
| W_decode₂ := "W_decode_2"
| h_decode := "h_decode"
| W_decode_p := "W_decode_p"
| μ := "mu"
| σ := "sigma"
| σ₂ := "sigma_sq"
| log_σ₂ := "log_s₂"
| z := "z"
| encoding_loss := "encoding_loss"
| decoding_loss := "decoding_loss"
| ε := "eps"
| x := "x"
| p := "p"

instance : has_to_string label := ⟨to_str⟩

def to_nat : label → ℕ
| default := 0
| batch_start := 1
| W_encode := 2
| W_encode₁ := 3
| W_encode₂ := 4
| h_encode := 5
| W_encode_μ := 6
| W_encode_logσ₂ := 7
| W_decode := 8
| W_decode₁ := 9
| W_decode₂ := 10
| h_decode := 11
| W_decode_p := 12
| μ := 13
| σ := 14
| σ₂ := 15
| log_σ₂ := 16
| z := 17
| encoding_loss := 18
| decoding_loss := 19
| ε := 20
| x := 21
| p := 22

section proofs
open tactic

meta def prove_neq_case_core : tactic unit :=
do H ← intro `H,
   dunfold_at [`certigrad.label.to_nat] H,
   H ← get_local `H,
   ty ← infer_type H,
   nty ← return $ expr.app (expr.const `not []) ty,
   assert `H_not nty,
   prove_nats_neq,
   exfalso,
   get_local `H_not >>= λ H_not, exact (expr.app H_not H)

--cases x, all_goals { cases y, all_goals { (prove_neq_case_core <|> (intro1 >> reflexivity)) } }
lemma label_eq_of_to_nat {x y : label} : x = y → to_nat x = to_nat y :=
begin
intro H,
subst H,
end

end proofs

def less_than (x y : label) : Prop := x^.to_nat < y^.to_nat

instance : has_lt label := ⟨less_than⟩

instance decidable_less_than (x y : label) : decidable (x < y) := by apply nat.decidable_lt

end label
end certigrad
