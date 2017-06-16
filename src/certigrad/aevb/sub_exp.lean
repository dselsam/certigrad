import .util .naive ..prove_model_ok ..pre

set_option class.instance_max_depth 1000000
set_option max_memory 10000000
set_option pp.max_depth 100000

namespace certigrad
namespace T



end T

section tactic
open tactic

meta def prove_is_mvn_integrable_core : tactic unit :=
first [
       applyc `certigrad.T.is_btw_id
     , applyc `certigrad.T.is_btw_const
     , applyc `certigrad.T.is_btw_sigmoid
     , applyc `certigrad.T.is_btw_softplus
     , applyc `certigrad.T.is_btw_gemm
     , applyc `certigrad.T.is_btw_neg
     , applyc `certigrad.T.is_btw_inv
     , applyc `certigrad.T.is_btw_add
     , applyc `certigrad.T.is_btw_mul
     , applyc `certigrad.T.is_btw_sub
     , applyc `certigrad.T.is_btw_div
     , applyc `certigrad.T.is_btw_exp

     , applyc `certigrad.T.is_linear_id
     , applyc `certigrad.T.is_linear_const
     , applyc `certigrad.T.is_linear_gemm
     , applyc `certigrad.T.is_linear_neg
     , applyc `certigrad.T.is_linear_inv
     , applyc `certigrad.T.is_linear_add
     , applyc `certigrad.T.is_linear_mul
     , applyc `certigrad.T.is_linear_sub
     , applyc `certigrad.T.is_linear_div
]

meta def prove_is_mvn_integrable : tactic unit :=
do applyc `certigrad.T.is_integrable_mvn_of_sub_exp,
   repeat_at_most 100 prove_is_mvn_integrable_core

end tactic

end certigrad
