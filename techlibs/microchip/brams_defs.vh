/*
ISC License

Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

`define PARAMS_INIT_LSRAM \
	.INIT0(slice_init_LSRAM(00)), \
	.INIT1(slice_init_LSRAM(01)), \
	.INIT2(slice_init_LSRAM(02)), \
	.INIT3(slice_init_LSRAM(03)), \
	.INIT4(slice_init_LSRAM(04)), \
	.INIT5(slice_init_LSRAM(05)), \
	.INIT6(slice_init_LSRAM(06)), \
	.INIT7(slice_init_LSRAM(07)), \
	.INIT8(slice_init_LSRAM(08)), \
	.INIT9(slice_init_LSRAM(09)), \
	.INIT10(slice_init_LSRAM(10)), \
	.INIT11(slice_init_LSRAM(11)), \
	.INIT12(slice_init_LSRAM(12)), \
	.INIT13(slice_init_LSRAM(13)), \
	.INIT14(slice_init_LSRAM(14)), \
	.INIT15(slice_init_LSRAM(15)), \
	.INIT16(slice_init_LSRAM(16)), \
	.INIT17(slice_init_LSRAM(17)), \
	.INIT18(slice_init_LSRAM(18)), \
	.INIT19(slice_init_LSRAM(19))

`define PARAMS_INIT_uSRAM \
	.INIT0(slice_init_uSRAM(00)), \
	.INIT1(slice_init_uSRAM(01)), \
	.INIT2(slice_init_uSRAM(02)), \
	.INIT3(slice_init_uSRAM(03)), \
	.INIT4(slice_init_uSRAM(04)), \
	.INIT5(slice_init_uSRAM(05)), \
	.INIT6(slice_init_uSRAM(06)), \
	.INIT7(slice_init_uSRAM(07)), \
	.INIT8(slice_init_uSRAM(08)), \
	.INIT9(slice_init_uSRAM(09)), \
	.INIT10(slice_init_uSRAM(10)), \
	.INIT11(slice_init_uSRAM(11)) \

// Helper function for initializing the LSRAM
function [1023:0] slice_init_LSRAM;
	input integer slice_idx;
	integer i;
	for (i = 0; i < 1024; i = i + 1)
		slice_init_LSRAM[i] = INIT[(slice_idx * 1024 + i)];
endfunction

// Helper function for initializing the uSRAM
function [63:0] slice_init_uSRAM;
	input integer slice_idx;
	integer i;
	for (i = 0; i < 64; i = i + 1)
		slice_init_uSRAM[i] = INIT[(slice_idx * 64 + i)];
endfunction