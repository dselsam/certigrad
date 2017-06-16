import .util .naive ..prove_model_ok ..pre .sub_exp

set_option class.instance_max_depth 1000000
set_option max_memory 10000000
set_option pp.max_depth 100000

namespace certigrad
namespace aevb

open certigrad.tactic


--set_option trace.simp_lemmas.rewrite.failure true
--set_option pp.notation false
--set_option trace.type_context.is_def_eq true
--set_option trace.type_context.is_def_eq_detail true

example (a : arch) (ws : weights a) (x_data : T [a^.n_in, a^.n_x]) :
T.is_integrable
    (λ (x : T [a.nz, a.bs]),
       T.mvn_iso_pdf 0 1 x ⬝
         T.gemm
           ((T.gemm (T.transpose (ws.W_encode_logσ₂))
                   ((T.gemm (T.transpose (ws.W_decode))
                               (T.gemm (T.transpose (ws.W_decode_p))
                                    (((1 - T.get_col_range (a.bs) x_data (T.round (ws.batch_start))) /
                                              (1 -
                                                 T.sigmoid
                                                   (T.gemm (ws.W_decode_p)
                                                      (T.softplus
                                                         (T.gemm (ws.W_decode)
                                                            (x *
                                                                 T.sqrt
                                                                   (T.exp
                                                                      (T.gemm (ws.W_encode_logσ₂)
                                                                         (T.softplus
                                                                            (T.gemm (ws.W_encode)
                                                                               (T.get_col_range (a.bs) x_data
                                                                                  (T.round (ws.batch_start))))))) +
                                                               T.gemm (ws.W_encode_μ)
                                                                 (T.softplus
                                                                    (T.gemm (ws.W_encode)
                                                                       (T.get_col_range (a.bs) x_data
                                                                          (T.round (ws.batch_start)))))))))) -

                                              (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)) /
                                                 T.sigmoid
                                                   (T.gemm (ws.W_decode_p)
                                                      (T.softplus
                                                         (T.gemm (ws.W_decode)
                                                            (x *
                                                                 T.sqrt
                                                                   (T.exp
                                                                      (T.gemm (ws.W_encode_logσ₂)
                                                                         (T.softplus
                                                                            (T.gemm (ws.W_encode)
                                                                               (T.get_col_range (a.bs) x_data
                                                                                  (T.round (ws.batch_start))))))) +
                                                               T.gemm (ws.W_encode_μ)
                                                                 (T.softplus
                                                                    (T.gemm (ws.W_encode)
                                                                       (T.get_col_range (a.bs) x_data
                                                                          (T.round (ws.batch_start))))))))))) *
                                         T.sigmoid
                                           (T.gemm (ws.W_decode_p)
                                              (T.softplus
                                                 (T.gemm (ws.W_decode)
                                                    (x *
                                                         T.sqrt
                                                           (T.exp
                                                              (T.gemm (ws.W_encode_logσ₂)
                                                                 (T.softplus
                                                                    (T.gemm (ws.W_encode)
                                                                       (T.get_col_range (a.bs) x_data
                                                                          (T.round (ws.batch_start))))))) +
                                                       T.gemm (ws.W_encode_μ)
                                                         (T.softplus
                                                            (T.gemm (ws.W_encode)
                                                               (T.get_col_range (a.bs) x_data
                                                                  (T.round (ws.batch_start))))))))) *
                                       (1 -
                                          T.sigmoid
                                            (T.gemm (ws.W_decode_p)
                                               (T.softplus
                                                  (T.gemm (ws.W_decode)
                                                     (x *
                                                          T.sqrt
                                                            (T.exp
                                                               (T.gemm (ws.W_encode_logσ₂)
                                                                  (T.softplus
                                                                     (T.gemm (ws.W_encode)
                                                                        (T.get_col_range (a.bs) x_data
                                                                           (T.round (ws.batch_start))))))) +
                                                        T.gemm (ws.W_encode_μ)
                                                          (T.softplus
                                                             (T.gemm (ws.W_encode)
                                                                (T.get_col_range (a.bs) x_data
                                                                   (T.round (ws.batch_start))))))))))) /
                                  (1 +
                                     T.exp
                                       (-T.gemm (ws.W_decode)
                                            (x *
                                                 T.sqrt
                                                   (T.exp
                                                      (T.gemm (ws.W_encode_logσ₂)
                                                         (T.softplus
                                                            (T.gemm (ws.W_encode)
                                                               (T.get_col_range (a.bs) x_data
                                                                  (T.round (ws.batch_start))))))) +
                                               T.gemm (ws.W_encode_μ)
                                                 (T.softplus
                                                    (T.gemm (ws.W_encode)
                                                       (T.get_col_range (a.bs) x_data
                                                          (T.round (ws.batch_start))))))))) *
                             x +
                             (T.sqrt
                                  (T.exp
                                     (T.gemm (ws.W_encode_logσ₂)
                                        (T.softplus
                                           (T.gemm (ws.W_encode)
                                              (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))) -
                                1 /
                                  T.sqrt
                                    (T.exp
                                       (T.gemm (ws.W_encode_logσ₂)
                                          (T.softplus
                                             (T.gemm (ws.W_encode)
                                                (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))))) /
                        (2 *
                           T.sqrt
                             (T.exp
                                (T.gemm (ws.W_encode_logσ₂)
                                   (T.softplus
                                      (T.gemm (ws.W_encode)
                                         (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)))))))) *
                      T.exp
                        (T.gemm (ws.W_encode_logσ₂)
                           (T.softplus
                              (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))) +
                 T.gemm (T.transpose (ws.W_encode_μ))
                   (T.gemm (T.transpose (ws.W_decode))
                        (T.gemm (T.transpose (ws.W_decode_p))
                             (((1 - T.get_col_range (a.bs) x_data (T.round (ws.batch_start))) /
                                       (1 -
                                          T.sigmoid
                                            (T.gemm (ws.W_decode_p)
                                               (T.softplus
                                                  (T.gemm (ws.W_decode)
                                                     (x *
                                                          T.sqrt
                                                            (T.exp
                                                               (T.gemm (ws.W_encode_logσ₂)
                                                                  (T.softplus
                                                                     (T.gemm (ws.W_encode)
                                                                        (T.get_col_range (a.bs) x_data
                                                                           (T.round (ws.batch_start))))))) +
                                                        T.gemm (ws.W_encode_μ)
                                                          (T.softplus
                                                             (T.gemm (ws.W_encode)
                                                                (T.get_col_range (a.bs) x_data
                                                                   (T.round (ws.batch_start)))))))))) -
                                       (T.get_col_range (a.bs) x_data (T.round (ws.batch_start)) /
                                          T.sigmoid
                                            (T.gemm (ws.W_decode_p)
                                               (T.softplus
                                                  (T.gemm (ws.W_decode)
                                                     (x *
                                                          T.sqrt
                                                            (T.exp
                                                               (T.gemm (ws.W_encode_logσ₂)
                                                                  (T.softplus
                                                                     (T.gemm (ws.W_encode)
                                                                        (T.get_col_range (a.bs) x_data
                                                                           (T.round (ws.batch_start))))))) +
                                                        T.gemm (ws.W_encode_μ)
                                                          (T.softplus
                                                             (T.gemm (ws.W_encode)
                                                                (T.get_col_range (a.bs) x_data
                                                                   (T.round (ws.batch_start))))))))))) *
                                  T.sigmoid
                                    (T.gemm (ws.W_decode_p)
                                       (T.softplus
                                          (T.gemm (ws.W_decode)
                                             (x *
                                                  T.sqrt
                                                    (T.exp
                                                       (T.gemm (ws.W_encode_logσ₂)
                                                          (T.softplus
                                                             (T.gemm (ws.W_encode)
                                                                (T.get_col_range (a.bs) x_data
                                                                   (T.round (ws.batch_start))))))) +
                                                T.gemm (ws.W_encode_μ)
                                                  (T.softplus
                                                     (T.gemm (ws.W_encode)
                                                        (T.get_col_range (a.bs) x_data
                                                           (T.round (ws.batch_start))))))))) *
                                (1 -
                                   T.sigmoid
                                     (T.gemm (ws.W_decode_p)
                                        (T.softplus
                                           (T.gemm (ws.W_decode)
                                              (x *
                                                   T.sqrt
                                                     (T.exp
                                                        (T.gemm (ws.W_encode_logσ₂)
                                                           (T.softplus
                                                              (T.gemm (ws.W_encode)
                                                                 (T.get_col_range (a.bs) x_data
                                                                    (T.round (ws.batch_start))))))) +
                                                 T.gemm (ws.W_encode_μ)
                                                   (T.softplus
                                                      (T.gemm (ws.W_encode)
                                                         (T.get_col_range (a.bs) x_data
                                                            (T.round (ws.batch_start))))))))))) /
                           (1 +
                              T.exp
                                (-T.gemm (ws.W_decode)
                                     (x *
                                          T.sqrt
                                            (T.exp
                                               (T.gemm (ws.W_encode_logσ₂)
                                                  (T.softplus
                                                     (T.gemm (ws.W_encode)
                                                        (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))) +
                                        T.gemm (ws.W_encode_μ)
                                          (T.softplus
                                             (T.gemm (ws.W_encode)
                                                (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))))) +
                        T.gemm (ws.W_encode_μ)
                          (T.softplus
                             (T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))) /
              (1 + T.exp (-T.gemm (ws.W_encode) (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))))
           (T.transpose (T.get_col_range (a.bs) x_data (T.round (ws.batch_start))))) :=
begin
prove_is_mvn_integrable,
end

end aevb
end certigrad
