(declare-datatype my_module_inputs ((my_module_inputs
  (my_module_inputs_b (_ BitVec 1))
  (my_module_inputs_a (_ BitVec 1))
)))
(declare-datatype my_module_outputs ((my_module_outputs
  (my_module_outputs_sum (_ BitVec 1))
)))
(declare-datatype my_module_state ((my_module_state
)))
(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))
(define-fun my_module_step ((inputs my_module_inputs) (current_state my_module_state)) (Pair my_module_outputs my_module_state)
  (let (((b (my_module_inputs_b inputs))))
  (let (((a (my_module_inputs_a inputs))))
  (let ((($add$tests/functional/single_bit/verilog/my_module_add.v_7$1$_Y (bvadd a b))))
    (pair 
      (my_module_outputs
        $add$tests/functional/single_bit/verilog/my_module_add.v_7$1$_Y    ; sum
      )
      (my_module_state
      )
    )
  )))
)
