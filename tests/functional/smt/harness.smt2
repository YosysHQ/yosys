(set-logic QF_UFBV)

; Declare sorts and functions as defined in the original file
(declare-sort |my_module_s| 0)
(declare-fun |my_module_is| (|my_module_s|) Bool)
(declare-fun |my_module#0| (|my_module_s|) (_ BitVec 1)) ; \a
(declare-fun |my_module#1| (|my_module_s|) (_ BitVec 1)) ; \b
(define-fun |my_module#2| ((state |my_module_s|)) (_ BitVec 1) (bvadd (|my_module#0| state) (|my_module#1| state))) ; $add$tests/functional/single_bit/verilog/my_module_add.v:7$1_Y

; Declare input witness functions
(define-fun |my_module_n a| ((state |my_module_s|)) Bool (= ((_ extract 0 0) (|my_module#0| state)) #b1))
(define-fun |my_module_n b| ((state |my_module_s|)) Bool (= ((_ extract 0 0) (|my_module#1| state)) #b1))

; Declare output function
(define-fun |my_module_n sum| ((state |my_module_s|)) Bool (= ((_ extract 0 0) (|my_module#2| state)) #b1))

; Other functions as defined in the original file
(define-fun |my_module_a| ((state |my_module_s|)) Bool true)
(define-fun |my_module_u| ((state |my_module_s|)) Bool true)
(define-fun |my_module_i| ((state |my_module_s|)) Bool true)
(define-fun |my_module_h| ((state |my_module_s|)) Bool true)
(define-fun |my_module_t| ((state |my_module_s|) (next_state |my_module_s|)) Bool true)

; Create a state variable
(declare-fun state0 () |my_module_s|)

; Assign inputs
(assert (= (|my_module#0| state0) #b1)) ; a = 1
(assert (= (|my_module#1| state0) #b0)) ; b = 0

; Check the output
(assert (|my_module_n sum| state0)) ; sum should be 1 (0 + 1 = 1)

; Check satisfiability
(check-sat)