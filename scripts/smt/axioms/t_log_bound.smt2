; SMT-LIB2 encoding for t_log_bound_for_sedt axiom
; 
; Axiom: t·log₂(3/2) ≤ β·(2^t + 3U) for t ≥ 3, U ≥ 1, β ≥ 1
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
(assert (>= beta 1.0))

; ==== Constants ====

; log(3/2) / log(2) ≈ 0.58496250072115618
(define-fun log_3_2_over_log_2 () Real 0.58496250072115618)

; ==== 2^t via explicit cases ====

; For integer t ∈ [3, 20], we list all 2^t values
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

; ==== Helper Definitions ====

; LHS: t · log₂(3/2)
(define-fun lhs () Real (* t log_3_2_over_log_2))

; RHS: β · (2^t + 3U)
(define-fun rhs () Real (* beta (+ pow_2_t (* 3.0 U))))

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
