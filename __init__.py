import os
import sys
sys.setdlopenflags(os.RTLD_NOW | os.RTLD_GLOBAL)

__all__ = ["libyosys"]
