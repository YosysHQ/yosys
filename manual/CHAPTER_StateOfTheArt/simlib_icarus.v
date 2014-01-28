
module cell0(Result0);
output Result0;
assign Result0 = 0;
endmodule

module cell1(Result0);
output Result0;
assign Result0 = 1;
endmodule

module ADD4(
	DataA0, DataA1, DataA2, DataA3,
	DataB0, DataB1, DataB2, DataB3,
	Result0, Result1, Result2, Result3, Cout
);
input DataA0, DataA1, DataA2, DataA3;
input DataB0, DataB1, DataB2, DataB3;
output Result0, Result1, Result2, Result3, Cout;
assign {Cout, Result3, Result2, Result1, Result0} = {DataA3, DataA2, DataA1, DataA0} + {DataB3, DataB2, DataB1, DataB0};
endmodule

module BUF(DATA, RESULT);
input DATA;
output RESULT;
assign RESULT = DATA;
endmodule

module INV(DATA, RESULT);
input DATA;
output RESULT;
assign RESULT = ~DATA;
endmodule

module fd4(
	Clock,
	Data0, Data1, Data2, Data3,
	Q0, Q1, Q2, Q3
);
input Clock;
input Data0, Data1, Data2, Data3;
output reg Q0, Q1, Q2, Q3;
always @(posedge Clock)
	{Q0, Q1, Q2, Q3} <= {Data0, Data1, Data2, Data3};
endmodule

module fdce1(
	Clock, Enable,
	Data0,
	Q0
);
input Clock, Enable;
input Data0;
output reg Q0;
always @(posedge Clock)
	if (Enable)
		Q0 <= Data0;
endmodule

module fdce4(
	Clock, Enable,
	Data0, Data1, Data2, Data3,
	Q0, Q1, Q2, Q3
);
input Clock, Enable;
input Data0, Data1, Data2, Data3;
output reg Q0, Q1, Q2, Q3;
always @(posedge Clock)
	if (Enable)
		{Q0, Q1, Q2, Q3} <= {Data0, Data1, Data2, Data3};
endmodule

module mux4_1_2(
	Sel0,
	Data0x0, Data0x1, Data0x2, Data0x3,
	Data1x0, Data1x1, Data1x2, Data1x3,
	Result0, Result1, Result2, Result3
);
input Sel0;
input Data0x0, Data0x1, Data0x2, Data0x3;
input Data1x0, Data1x1, Data1x2, Data1x3;
output Result0, Result1, Result2, Result3;
assign {Result0, Result1, Result2, Result3} = Sel0 ? {Data1x0, Data1x1, Data1x2, Data1x3} : {Data0x0, Data0x1, Data0x2, Data0x3};
endmodule

module mux1_1_2(
	Sel0,
	Data0x0,
	Data1x0,
	Result0
);
input Sel0;
input Data0x0;
input Data1x0;
output Result0;
assign Result0 = Sel0 ? Data1x0 : Data0x0;
endmodule

module xor2(
	DATA0X0,
	DATA1X0,
	RESULT0
);
input DATA0X0;
input DATA1X0;
output RESULT0;
assign RESULT0 = DATA1X0 ^ DATA0X0;
endmodule

module fdce64(
	Clock, Enable,
	Data0, Data1, Data2, Data3, Data4, Data5, Data6, Data7, Data8, Data9, Data10, Data11, Data12, Data13, Data14, Data15, Data16, Data17, Data18, Data19, Data20, Data21, Data22, Data23, Data24, Data25, Data26, Data27, Data28, Data29, Data30, Data31, Data32, Data33, Data34, Data35, Data36, Data37, Data38, Data39, Data40, Data41, Data42, Data43, Data44, Data45, Data46, Data47, Data48, Data49, Data50, Data51, Data52, Data53, Data54, Data55, Data56, Data57, Data58, Data59, Data60, Data61, Data62, Data63,
	Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15, Q16, Q17, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27, Q28, Q29, Q30, Q31, Q32, Q33, Q34, Q35, Q36, Q37, Q38, Q39, Q40, Q41, Q42, Q43, Q44, Q45, Q46, Q47, Q48, Q49, Q50, Q51, Q52, Q53, Q54, Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63
);
input Clock, Enable;
input Data0, Data1, Data2, Data3, Data4, Data5, Data6, Data7, Data8, Data9, Data10, Data11, Data12, Data13, Data14, Data15, Data16, Data17, Data18, Data19, Data20, Data21, Data22, Data23, Data24, Data25, Data26, Data27, Data28, Data29, Data30, Data31, Data32, Data33, Data34, Data35, Data36, Data37, Data38, Data39, Data40, Data41, Data42, Data43, Data44, Data45, Data46, Data47, Data48, Data49, Data50, Data51, Data52, Data53, Data54, Data55, Data56, Data57, Data58, Data59, Data60, Data61, Data62, Data63;
output reg Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15, Q16, Q17, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27, Q28, Q29, Q30, Q31, Q32, Q33, Q34, Q35, Q36, Q37, Q38, Q39, Q40, Q41, Q42, Q43, Q44, Q45, Q46, Q47, Q48, Q49, Q50, Q51, Q52, Q53, Q54, Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63;
always @(posedge Clock)
	if (Enable)
		{ Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15, Q16, Q17, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27, Q28, Q29, Q30, Q31, Q32, Q33, Q34, Q35, Q36, Q37, Q38, Q39, Q40, Q41, Q42, Q43, Q44, Q45, Q46, Q47, Q48, Q49, Q50, Q51, Q52, Q53, Q54, Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63 } <= { Data0, Data1, Data2, Data3, Data4, Data5, Data6, Data7, Data8, Data9, Data10, Data11, Data12, Data13, Data14, Data15, Data16, Data17, Data18, Data19, Data20, Data21, Data22, Data23, Data24, Data25, Data26, Data27, Data28, Data29, Data30, Data31, Data32, Data33, Data34, Data35, Data36, Data37, Data38, Data39, Data40, Data41, Data42, Data43, Data44, Data45, Data46, Data47, Data48, Data49, Data50, Data51, Data52, Data53, Data54, Data55, Data56, Data57, Data58, Data59, Data60, Data61, Data62, Data63 };
endmodule

module mux4_4_16(
	Sel0, Sel1, Sel2, Sel3,
	Result0, Result1, Result2, Result3,
	Data0x0, Data0x1, Data0x2, Data0x3,
	Data1x0, Data1x1, Data1x2, Data1x3,
	Data2x0, Data2x1, Data2x2, Data2x3,
	Data3x0, Data3x1, Data3x2, Data3x3,
	Data4x0, Data4x1, Data4x2, Data4x3,
	Data5x0, Data5x1, Data5x2, Data5x3,
	Data6x0, Data6x1, Data6x2, Data6x3,
	Data7x0, Data7x1, Data7x2, Data7x3,
	Data8x0, Data8x1, Data8x2, Data8x3,
	Data9x0, Data9x1, Data9x2, Data9x3,
	Data10x0, Data10x1, Data10x2, Data10x3,
	Data11x0, Data11x1, Data11x2, Data11x3,
	Data12x0, Data12x1, Data12x2, Data12x3,
	Data13x0, Data13x1, Data13x2, Data13x3,
	Data14x0, Data14x1, Data14x2, Data14x3,
	Data15x0, Data15x1, Data15x2, Data15x3
);
input Sel0, Sel1, Sel2, Sel3;
output Result0, Result1, Result2, Result3;
input Data0x0, Data0x1, Data0x2, Data0x3;
input Data1x0, Data1x1, Data1x2, Data1x3;
input Data2x0, Data2x1, Data2x2, Data2x3;
input Data3x0, Data3x1, Data3x2, Data3x3;
input Data4x0, Data4x1, Data4x2, Data4x3;
input Data5x0, Data5x1, Data5x2, Data5x3;
input Data6x0, Data6x1, Data6x2, Data6x3;
input Data7x0, Data7x1, Data7x2, Data7x3;
input Data8x0, Data8x1, Data8x2, Data8x3;
input Data9x0, Data9x1, Data9x2, Data9x3;
input Data10x0, Data10x1, Data10x2, Data10x3;
input Data11x0, Data11x1, Data11x2, Data11x3;
input Data12x0, Data12x1, Data12x2, Data12x3;
input Data13x0, Data13x1, Data13x2, Data13x3;
input Data14x0, Data14x1, Data14x2, Data14x3;
input Data15x0, Data15x1, Data15x2, Data15x3;
assign {Result0, Result1, Result2, Result3} =
	{Sel3, Sel2, Sel1, Sel0} == 0 ? { Data0x0, Data0x1, Data0x2, Data0x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 1 ? { Data1x0, Data1x1, Data1x2, Data1x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 2 ? { Data2x0, Data2x1, Data2x2, Data2x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 3 ? { Data3x0, Data3x1, Data3x2, Data3x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 4 ? { Data4x0, Data4x1, Data4x2, Data4x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 5 ? { Data5x0, Data5x1, Data5x2, Data5x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 6 ? { Data6x0, Data6x1, Data6x2, Data6x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 7 ? { Data7x0, Data7x1, Data7x2, Data7x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 8 ? { Data8x0, Data8x1, Data8x2, Data8x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 9 ? { Data9x0, Data9x1, Data9x2, Data9x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 10 ? { Data10x0, Data10x1, Data10x2, Data10x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 11 ? { Data11x0, Data11x1, Data11x2, Data11x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 12 ? { Data12x0, Data12x1, Data12x2, Data12x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 13 ? { Data13x0, Data13x1, Data13x2, Data13x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 14 ? { Data14x0, Data14x1, Data14x2, Data14x3 } :
	{Sel3, Sel2, Sel1, Sel0} == 15 ? { Data15x0, Data15x1, Data15x2, Data15x3 } : 'bx;
endmodule

module mux1_5_32(
	Sel0, Sel1, Sel2, Sel3, Sel4,
	Data0x0, Data1x0, Data2x0, Data3x0, Data4x0, Data5x0, Data6x0, Data7x0, Data8x0, Data9x0, Data10x0, Data11x0, Data12x0, Data13x0, Data14x0, Data15x0,
	Data16x0, Data17x0, Data18x0, Data19x0, Data20x0, Data21x0, Data22x0, Data23x0, Data24x0, Data25x0, Data26x0, Data27x0, Data28x0, Data29x0, Data30x0, Data31x0,
	Result0
);
input Sel0, Sel1, Sel2, Sel3, Sel4;
input Data0x0, Data1x0, Data2x0, Data3x0, Data4x0, Data5x0, Data6x0, Data7x0, Data8x0, Data9x0, Data10x0, Data11x0, Data12x0, Data13x0, Data14x0, Data15x0;
input Data16x0, Data17x0, Data18x0, Data19x0, Data20x0, Data21x0, Data22x0, Data23x0, Data24x0, Data25x0, Data26x0, Data27x0, Data28x0, Data29x0, Data30x0, Data31x0;
output Result0;
assign Result0 =
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 0 ? Data0x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 1 ? Data1x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 2 ? Data2x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 3 ? Data3x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 4 ? Data4x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 5 ? Data5x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 6 ? Data6x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 7 ? Data7x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 8 ? Data8x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 9 ? Data9x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 10 ? Data10x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 11 ? Data11x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 12 ? Data12x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 13 ? Data13x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 14 ? Data14x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 15 ? Data15x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 16 ? Data16x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 17 ? Data17x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 18 ? Data18x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 19 ? Data19x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 20 ? Data20x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 21 ? Data21x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 22 ? Data22x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 23 ? Data23x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 24 ? Data24x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 25 ? Data25x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 26 ? Data26x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 27 ? Data27x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 28 ? Data28x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 29 ? Data29x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 30 ? Data30x0 :
	{Sel4, Sel3, Sel2, Sel1, Sel0} == 31 ? Data31x0 : 'bx;
endmodule

