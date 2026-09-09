set -e
DIR=$(cd "$(dirname "$0")" && pwd)

run_cmp_test()
{
  cmp=$1
  log=${DIR}/map_cmp_${cmp}_eq.log

  echo "Running ${DIR}/map_cmp.v with CMP=4'd${cmp}.."
  ${YOSYS} -D "CMP_VALUE=4'd${cmp}" -q -s ${DIR}/check_map.ys -l ${log} -f verilog ${DIR}/map_cmp.v
}

cmp=0
while [ ${cmp} -lt 16 ]; do
  run_cmp_test ${cmp}
  cmp=$((cmp + 1))
done

for x in ${DIR}/*.v; do
  echo "Running $x.."
  ${YOSYS} -q -s ${DIR}/check_map.ys -l ${x%.v}.log -f verilog $x
done
for x in ${DIR}/map_cmp.v; do
  echo "Running $x.."
  ${YOSYS} -q -s ${DIR}/check_map_lut6.ys -l ${x%.v}_lut6.log -f verilog $x
done
