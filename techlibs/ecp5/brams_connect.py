#!/usr/bin/env python3

def write_bus_ports(f, ada_bits, adb_bits, dia_bits, dob_bits):
    ada_conn = [".ADA%d(%s)" % (i, ada_bits[i]) for i in range(len(ada_bits))]
    adb_conn = [".ADB%d(%s)" % (i, adb_bits[i]) for i in range(len(adb_bits))]
    dia_conn = [".DIA%d(%s)" % (i, dia_bits[i]) for i in range(len(dia_bits))]
    dob_conn = [".DOB%d(%s)" % (i, dob_bits[i]) for i in range(len(dob_bits))]
    print("    %s," % ", ".join(ada_conn), file=f)
    print("    %s," % ", ".join(adb_conn), file=f)
    print("    %s," % ", ".join(dia_conn), file=f)
    print("    %s," % ", ".join(dob_conn), file=f)

with open("techlibs/ecp5/bram_conn_1.vh", "w") as f:
    ada_bits = ["A1ADDR[%d]" % i for i in range(14)]
    adb_bits = ["B1ADDR[%d]" % i for i in range(14)]
    dia_bits = ["A1DATA[0]"] + ["1'b0" for i in range(17)]
    dob_bits = ["B1DATA[0]"]
    write_bus_ports(f, ada_bits, adb_bits, dia_bits, dob_bits)

with open("techlibs/ecp5/bram_conn_2.vh", "w") as f:
    ada_bits = ["1'b0"] + ["A1ADDR[%d]" % i for i in range(13)]
    adb_bits = ["1'b0"] + ["B1ADDR[%d]" % i for i in range(13)]
    dia_bits = ["A1DATA[%d]" % i for i in range(2)] + ["1'b0" for i in range(16)]
    dob_bits = ["B1DATA[%d]" % i for i in range(2)]
    write_bus_ports(f, ada_bits, adb_bits, dia_bits, dob_bits)

with open("techlibs/ecp5/bram_conn_4.vh", "w") as f:
    ada_bits = ["1'b0", "1'b0"] + ["A1ADDR[%d]" % i for i in range(12)]
    adb_bits = ["1'b0", "1'b0"] + ["B1ADDR[%d]" % i for i in range(12)]
    dia_bits = ["A1DATA[%d]" % i for i in range(4)] + ["1'b0" for i in range(14)]
    dob_bits = ["B1DATA[%d]" % i for i in range(4)]
    write_bus_ports(f, ada_bits, adb_bits, dia_bits, dob_bits)

with open("techlibs/ecp5/bram_conn_9.vh", "w") as f:
    ada_bits = ["1'b0", "1'b0", "1'b0"] + ["A1ADDR[%d]" % i for i in range(11)]
    adb_bits = ["1'b0", "1'b0", "1'b0"] + ["B1ADDR[%d]" % i for i in range(11)]
    dia_bits = ["A1DATA[%d]" % i for i in range(9)] + ["1'b0" for i in range(9)]
    dob_bits = ["B1DATA[%d]" % i for i in range(9)]
    write_bus_ports(f, ada_bits, adb_bits, dia_bits, dob_bits)

with open("techlibs/ecp5/bram_conn_18.vh", "w") as f:
    ada_bits = ["A1EN[0]", "A1EN[1]", "1'b0", "1'b0"] + ["A1ADDR[%d]" % i for i in range(10)]
    adb_bits = ["1'b0", "1'b0", "1'b0", "1'b0"] + ["B1ADDR[%d]" % i for i in range(10)]
    dia_bits = ["A1DATA[%d]" % i for i in range(18)]
    dob_bits = ["B1DATA[%d]" % i for i in range(18)]
    write_bus_ports(f, ada_bits, adb_bits, dia_bits, dob_bits)
