# M10K 20-bit byte enables

Run this regression with an installation containing the paired `intel_alm`
techlib files:

```sh
python3 tests/arch/intel_alm/m10k_byte_enable/regression.py \
  --yosys /path/to/install/bin/yosys --output /tmp/m10k-byte-enable
```

The test infers one 512x20 `MISTRAL_M10K` with `CFG_BYTE_ENABLE=1`, verifies
two independent `A1BE` bits and a separate logical write enable, then proves a
12-step mapped-versus-reference model. The proof covers both 10-bit lanes,
write-enable gating, read-enable hold, independent clocks and initialized data.
Other M10K widths retain the existing one-bit enable inference.
