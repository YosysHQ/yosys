
example.edif: example.ys example.v example.constr osu035_stdcells.lib
	yosys -l example.yslog -q example.ys

osu035_stdcells.lib:
	rm -f osu035_stdcells.lib.part osu035_stdcells.lib
	wget -O osu035_stdcells.lib.part https://vlsiarch.ecen.okstate.edu/flows/MOSIS_SCMOS/latest/cadence/lib/ami035/signalstorm/osu035_stdcells.lib
	mv osu035_stdcells.lib.part osu035_stdcells.lib

clean:
	rm -f osu035_stdcells.lib
	rm -f example.yslog example.edif

