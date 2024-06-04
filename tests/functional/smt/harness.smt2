; Load the datatypes and function definitions
(declare-datatype my_module_inputs ((my_module_inputs
  (my_module_inputs_b (_ BitVec 1))
  (my_module_inputs_a (_ BitVec 1))
)))
(declare-datatype my_module_outputs ((my_module_outputs
  (my_module_outputs_sum (_ BitVec 1))
)))
; (declare-datatype my_module_state (()))

(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))

(define-fun my_module_step ((inputs my_module_inputs)) my_module_outputs
  (let ((b (my_module_inputs_b inputs))
        (a (my_module_inputs_a inputs))
        (sum (bvadd a b)))
      (my_module_outputs sum)
  )
)

; Create input values
(declare-const input_a (_ BitVec 1))
(declare-const input_b (_ BitVec 1))
; (declare-const initial_state my_module_state)

; Define input values
(assert (= input_a #b1)) ; or #b0 for 0
(assert (= input_b #b0)) ; or #b1 for 1

; Construct the input object
(define-const inputs my_module_inputs (my_module_inputs input_b input_a))

; Call the step function
(define-const result my_module_outputs (my_module_step inputs))

; Extract the output
(define-const output_sum (_ BitVec 1) (my_module_outputs_sum result))

; Check the output
(check-sat)
(get-value (output_sum))