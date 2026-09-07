#!/bin/sh
# Run on the designated target under its kit.py lease after loading top.v's RBF.
# HPS GP access only: this script does not program or stop the FPGA.
set -eu
read_gpi() { busybox devmem 0xFF706014 32; }
write_gpo() { busybox devmem 0xFF706010 32 "$1"; }
check() {
    write_gpo "$1"
    sleep 0.01
    status=$(read_gpi)
    [ "$(((status >> 16) & 65535))" -eq 54288 ] || {
        echo "FAIL: expected 040 MLAB signature: $status" >&2; exit 1;
    }
    actual=$((status & 255))
    [ "$actual" -eq "$2" ] || {
        echo "FAIL: address=$1 expected=$2 actual=$actual" >&2; exit 1;
    }
}
address=0
while [ "$address" -lt 32 ]; do
    check "$address" "$((((address * 73) ^ (address >> 1) ^ 166) & 255))"
    address=$((address + 1))
done
echo 'PASS: all 32 initialized bytes'
address=0
while [ "$address" -lt 32 ]; do
    value=$(((address * 19 + 83) & 255))
    write_gpo "$(((value << 8) | address))"
    write_gpo "$((65536 | (value << 8) | address))"
    sleep 0.01
    write_gpo "$(((value << 8) | address))"
    address=$((address + 2))
done
address=0
while [ "$address" -lt 32 ]; do
    if [ "$((address & 1))" -eq 0 ]; then
        value=$(((address * 19 + 83) & 255))
    else
        value=$((((address * 73) ^ (address >> 1) ^ 166) & 255))
    fi
    check "$address" "$value"
    address=$((address + 1))
done
echo 'PASS: writes update alternate addresses and preserve unwritten bytes'
