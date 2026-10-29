typedef logic signed [3:0] operand_t;

module typedef_signed_element_source(output operand_t value);
	assign value = -2;
endmodule

module typedef_signed_element(
	input operand_t [1:0] operands,
	output logic [7:0] element,
	output logic [15:0] array,
	output logic [7:0] driven_element,
	output logic [7:0] driven_member
);
	operand_t [0:0] driven;
	struct packed { operand_t value; } member;
	typedef_signed_element_source source(driven[0]);
	typedef_signed_element_source member_source(member.value);
	assign element = operands[0];
	assign array = operands;
	assign driven_element = driven[0];
	assign driven_member = member.value;
endmodule
