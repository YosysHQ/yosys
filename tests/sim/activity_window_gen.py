"""Generate three VCDs with identical stimulus, shifted to different points in time.

The shifts reproduce a customer dump at a 1fs timescale whose last timestamp was
5_587_907_000: far past INT_MAX, so 32-bit time handling wraps. `late` puts the whole
window beyond INT_MAX, so every timestamp wraps by the same amount; `cross` straddles
INT_MAX, so time appears to run backwards partway through the dump. Activity annotation
measures a *window*, so all three dumps must annotate identically.

The stimulus is periodic over the window: the value at t=0 equals the value at
t=duration and the window holds a whole number of data periods. That makes every
expected number exact (see activity_window.ys), with no partial interval at either edge.

  clk  1GHz, rises at k*P              duty 0.500  activity 1.000
  a    period 4 cycles, 50% high       duty 0.500  activity 0.250
  b    period 8 cycles, 50% high       duty 0.500  activity 0.125
  c    constant high                   duty 1.000  activity 0.000
  d    period 8 cycles, 25% high       duty 0.250  activity 0.125

Yosys reports activity as toggles/(2*cycles), so a signal whose period is N cycles has
activity 1/N: two toggles per period, spread over N cycles, halved.
"""

import sys

PERIOD = 1_000_000  # 1ns clock in fs -> 1GHz
CYCLES = 128  # window length in clock cycles; a multiple of every data period
LATE_SHIFT = 5_320_000_000  # whole window past INT_MAX
CROSS_SHIFT = 2_147_400_000  # window straddles INT_MAX (2_147_483_647)

HEADER = """$timescale 1fs $end
$scope module tb $end
$scope module uut $end
$var wire 1 ! clk $end
$var wire 1 " a $end
$var wire 1 # b $end
$var wire 1 $ c $end
$var wire 1 % d $end
$upscope $end
$upscope $end
$enddefinitions $end
"""


def write(path, shift):
  # time -> [(vcd_id, value)], so edges that coincide share one timestamp block
  timeline = {}

  def at(t, vid, val):
    timeline.setdefault(t, []).append((vid, val))

  # Initial sample. The first sample seeds the value; it is not a toggle.
  for vid, val in (("!", 1), ('"', 1), ("#", 0), ("$", 1), ("%", 0)):
    at(0, vid, val)

  for k in range(CYCLES):
    # Clock: high for the first half of every cycle. The final rise at CYCLES*P below
    # closes the window, so the window holds exactly CYCLES high pulses of P/2.
    at(k * PERIOD + PERIOD // 2, "!", 0)
    if k:
      at(k * PERIOD, "!", 1)

    # Data switches mid-cycle, half a period off the clock edges, so no data edge lands
    # on the closing sample and gets counted as an extra toggle.
    t = k * PERIOD + PERIOD // 2
    if k % 2 == 0:
      at(t, '"', 0 if k % 4 == 0 else 1)  # a: 4-cycle period
    if k % 4 == 0:
      at(t, "#", 1 if k % 8 == 0 else 0)  # b: 8-cycle period
    if k % 8 == 0:
      at(t, "%", 1)  # d: 8-cycle period, high for 2 cycles
    if k % 8 == 2:
      at(t, "%", 0)

  at(CYCLES * PERIOD, "!", 1)

  with open(path, "w", encoding="utf-8") as f:
    f.write(HEADER)
    for t in sorted(timeline):
      f.write(f"#{t + shift}\n")
      for vid, val in timeline[t]:
        f.write(f"{val}{vid}\n")


for arg, shift in zip(sys.argv[1:4], (0, LATE_SHIFT, CROSS_SHIFT)):
  write(arg, shift)
  stop = shift + CYCLES * PERIOD
  as_int32 = (stop + 2**31) % 2**32 - 2**31
  print(f"{arg}: {shift} .. {stop} fs, stop as int32 {as_int32}")
