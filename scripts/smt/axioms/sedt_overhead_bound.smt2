; SMT-LIB2 encoding for sedt_overhead_bound axiom
; 
; Axiom: β·2^t + β·max(2·2^{t-2}, 3t) + t·log₂(3/2) ≤ β·C(t,U)
;        where C(t,U) = 2·2^t + 3t + 3U
;
; Strategy: We negate the inequality and search for a counterexample.
; If UNSAT, the axiom holds. If SAT, we found a counterexample.
;
; NOTE: We use integer t for finite verification (t ∈ {3,4,5,...,20})

(set-logic QF_NRA)  ; Nonlinear Real Arithmetic
(set-option :produce-models true)

; ==== Declarations ====

(declare-const t Real)
(declare-const U Real)
(declare-const beta Real)

; ==== Preconditions ====

(assert (>= t 3.0))
(assert (<= t 20.0))  ; Finite bound for verification
(assert (>= U 1.0))
(assert (<= U 100.0)) ; Reasonable bound for U
(assert (>= beta 1.0))

; ==== Constants ====

; log(3/2) / log(2) ≈ 0.58496250072115618
(define-fun log_3_2_over_log_2 () Real 0.58496250072115618)

; ==== 2^t via explicit cases ====

(declare-const pow_2_t Real)

(assert 
  (or 
    (and (= t 3.0) (= pow_2_t 8.0))
    (and (= t 4.0) (= pow_2_t 16.0))
    (and (= t 5.0) (= pow_2_t 32.0))
    (and (= t 6.0) (= pow_2_t 64.0))
    (and (= t 7.0) (= pow_2_t 128.0))
    (and (= t 8.0) (= pow_2_t 256.0))
    (and (= t 9.0) (= pow_2_t 512.0))
    (and (= t 10.0) (= pow_2_t 1024.0))
    (and (= t 11.0) (= pow_2_t 2048.0))
    (and (= t 12.0) (= pow_2_t 4096.0))
    (and (= t 13.0) (= pow_2_t 8192.0))
    (and (= t 14.0) (= pow_2_t 16384.0))
    (and (= t 15.0) (= pow_2_t 32768.0))
    (and (= t 16.0) (= pow_2_t 65536.0))
    (and (= t 17.0) (= pow_2_t 131072.0))
    (and (= t 18.0) (= pow_2_t 262144.0))
    (and (= t 19.0) (= pow_2_t 524288.0))
    (and (= t 20.0) (= pow_2_t 1048576.0))
  )
)

; ==== 2^{t-2} via explicit cases ====

(declare-const pow_2_t_minus_2 Real)

(assert 
  (or 
    (and (= t 3.0) (= pow_2_t_minus_2 2.0))
    (and (= t 4.0) (= pow_2_t_minus_2 4.0))
    (and (= t 5.0) (= pow_2_t_minus_2 8.0))
    (and (= t 6.0) (= pow_2_t_minus_2 16.0))
    (and (= t 7.0) (= pow_2_t_minus_2 32.0))
    (and (= t 8.0) (= pow_2_t_minus_2 64.0))
    (and (= t 9.0) (= pow_2_t_minus_2 128.0))
    (and (= t 10.0) (= pow_2_t_minus_2 256.0))
    (and (= t 11.0) (= pow_2_t_minus_2 512.0))
    (and (= t 12.0) (= pow_2_t_minus_2 1024.0))
    (and (= t 13.0) (= pow_2_t_minus_2 2048.0))
    (and (= t 14.0) (= pow_2_t_minus_2 4096.0))
    (and (= t 15.0) (= pow_2_t_minus_2 8192.0))
    (and (= t 16.0) (= pow_2_t_minus_2 16384.0))
    (and (= t 17.0) (= pow_2_t_minus_2 32768.0))
    (and (= t 18.0) (= pow_2_t_minus_2 65536.0))
    (and (= t 19.0) (= pow_2_t_minus_2 131072.0))
    (and (= t 20.0) (= pow_2_t_minus_2 262144.0))
  )
)

; ==== Helper Definitions ====

; K_glue(t) = max(2·2^{t-2}, 3t)
(declare-const K_glue Real)
(assert (or (and (>= (* 2.0 pow_2_t_minus_2) (* 3.0 t))
                 (= K_glue (* 2.0 pow_2_t_minus_2)))
            (and (< (* 2.0 pow_2_t_minus_2) (* 3.0 t))
                 (= K_glue (* 3.0 t)))))

; C(t,U) = 2·2^t + 3t + 3U
(define-fun C_t_U () Real
  (+ (* 2.0 pow_2_t) (* 3.0 t) (* 3.0 U)))

; LHS: β·2^t + β·K_glue + t·log₂(3/2)
(define-fun lhs () Real
  (+ (* beta pow_2_t)
     (* beta K_glue)
     (* t log_3_2_over_log_2)))

; RHS: β·C(t,U)
(define-fun rhs () Real (* beta C_t_U))

; ==== Main Inequality (NEGATED) ====

; Original: lhs ≤ rhs
; Negated: lhs > rhs (searching for counterexample)

(assert (> lhs rhs))

; ==== Check Satisfiability ====

(check-sat)

; If SAT: get counterexample
(get-model)

; ==== Expected Result ====
; UNSAT — no counterexample exists, axiom holds for t ∈ [3,20]
; SAT — counterexample found, axiom may be incorrect

