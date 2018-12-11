PYTHONPATH=`pwd`/../../:$PYTHONPATH
mkdir -p out
if [ ! -f ../../libyosys.so ]; then
	make -C ../..
fi
python3.5 netlist_graph.py
