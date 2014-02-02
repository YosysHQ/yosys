
all: proc_00.pdf proc_01.pdf proc_02.pdf

proc_00.pdf: proc_00.v proc_00.ys
	../../yosys -p 'script proc_00.ys; show -notitle -prefix proc_00 -format pdf'

proc_01.pdf: proc_01.v proc_01.ys
	../../yosys -p 'script proc_01.ys; show -notitle -prefix proc_01 -format pdf'

proc_02.pdf: proc_02.v proc_02.ys
	../../yosys -p 'script proc_02.ys; show -notitle -prefix proc_02 -format pdf'

