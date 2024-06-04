(set-logic QF_BV)

; Declarations from functional_add.smt2
(declare-datatype my_module_inputs ((my_module_inputs
  (my_module_inputs_b (_ BitVec 1))
  (my_module_inputs_a (_ BitVec 1))
)))
(declare-datatype my_module_outputs ((my_module_outputs
  (my_module_outputs_sum (_ BitVec 1))
)))
(declare-datatype my_module_state ((my_module_state)))
(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))

; Declarations from old_add.smt2
(declare-sort |my_module_s| 0)
(declare-fun |my_module#0| (|my_module_s|) (_ BitVec 1)) ; \a
(declare-fun |my_module#1| (|my_module_s|) (_ BitVec 1)) ; \b
(define-fun |my_module#2| ((state |my_module_s|)) (_ BitVec 1) (bvadd (|my_module#0| state) (|my_module#1| state))) ; $add$tests/functional/single_bit/verilog/my_module_add.v:7$1_Y

; Input variables
(declare-const inputs my_module_inputs)

; Instantiate functional_add
(define-fun functional_add ((inputs my_module_inputs)) (_ BitVec 1)
  (let ((a (my_module_inputs_a inputs))
        (b (my_module_inputs_b inputs)))
    (bvadd a b)
  )
)

; Instantiate old_add
(define-fun old_add ((inputs my_module_inputs)) (_ BitVec 1)
  (let ((a (my_module_inputs_a inputs))
        (b (my_module_inputs_b inputs)))
    (bvadd a b)
  )
)

; Assert equivalence
(assert (not (= (functional_add inputs) (old_add inputs))))

; Check satisfiability
(check-sat)